use ruff_python_ast::name::Name;

use super::enums::enum_member_literals;
use super::{Truthiness, Type, UnionType};
use crate::{
    Db,
    place::PlaceAndQualifiers,
    types::{
        CallArguments, IntersectionType, KnownClass, MemberLookupPolicy, TypeContext,
        TypeVarBoundOrConstraints, UnionBuilder,
    },
};

pub(super) fn evaluate_type_equality<'db>(
    db: &'db dyn Db,
    left: Type<'db>,
    right: Type<'db>,
) -> EqualityResult<'db> {
    let special_case = equality_special_case(db, left, right);

    if special_case != EqualityResult::Ambiguous {
        return special_case;
    }

    let Ok(eq_bindings) = left.try_call_dunder(
        db,
        "__eq__",
        CallArguments::positional([right]),
        TypeContext::default(),
    ) else {
        return EqualityResult::Ambiguous;
    };
    let Ok(ne_bindings) = left.try_call_dunder(
        db,
        "__ne__",
        CallArguments::positional([right]),
        TypeContext::default(),
    ) else {
        return EqualityResult::Ambiguous;
    };
    let eq_truthiness = eq_bindings.return_type(db).bool(db);
    if eq_truthiness == Truthiness::Ambiguous {
        return EqualityResult::Ambiguous;
    }
    let ne_truthiness = ne_bindings.return_type(db).bool(db);
    if ne_truthiness == eq_truthiness {
        EqualityResult::Ambiguous
    } else {
        match eq_truthiness {
            Truthiness::AlwaysTrue => EqualityResult::AlwaysEqual,
            Truthiness::AlwaysFalse => EqualityResult::AlwaysUnequal,
            Truthiness::Ambiguous => EqualityResult::Ambiguous,
        }
    }
}

fn equality_special_case<'db>(
    db: &'db dyn Db,
    left: Type<'db>,
    right: Type<'db>,
) -> EqualityResult<'db> {
    match (left, right) {
        (
            Type::Never
            | Type::Dynamic(_)
            | Type::AlwaysFalsy
            | Type::AlwaysTruthy
            | Type::ProtocolInstance(_)
            | Type::DataclassTransformer(_)
            | Type::TypeGuard(_)
            | Type::TypeIs(_),
            _,
        )
        | (
            _,
            Type::Never
            | Type::Dynamic(_)
            | Type::AlwaysFalsy
            | Type::AlwaysTruthy
            | Type::ProtocolInstance(_)
            | Type::DataclassTransformer(_)
            | Type::TypeGuard(_)
            | Type::TypeIs(_),
        ) => EqualityResult::Ambiguous,

        (Type::TypeAlias(alias), other) | (other, Type::TypeAlias(alias)) => {
            equality_special_case(db, alias.value_type(db), other)
        }

        (Type::TypeVar(var), other) | (other, Type::TypeVar(var)) => {
            match var.typevar(db).bound_or_constraints(db) {
                None => EqualityResult::Ambiguous,
                Some(TypeVarBoundOrConstraints::UpperBound(bound)) => {
                    equality_special_case(db, bound, other)
                }
                Some(TypeVarBoundOrConstraints::Constraints(constraints)) => {
                    equality_special_case(db, constraints.as_type(db), other)
                }
            }
        }

        (Type::NewTypeInstance(newtype), other) | (other, Type::NewTypeInstance(newtype)) => {
            equality_special_case(db, newtype.concrete_base_type(db), other)
        }

        (Type::Union(union), other) | (other, Type::Union(union)) => {
            // Check if the union is on the left (being narrowed) or right (compared against)
            let union_is_left = matches!(left, Type::Union(_));

            let mut narrowed_union = UnionBuilder::new(db);
            let mut has_ambiguous = false;
            let mut has_always_unequal = false;
            let mut always_equal_union = UnionBuilder::new(db);

            for element in union.elements(db) {
                match equality_special_case(db, *element, other) {
                    EqualityResult::AlwaysEqual => {
                        narrowed_union = narrowed_union.add(*element);
                        always_equal_union = always_equal_union.add(*element);
                    }
                    EqualityResult::Ambiguous => {
                        has_ambiguous = true;
                        narrowed_union = narrowed_union.add(*element);
                    }
                    EqualityResult::InequalityIndicatesNegativeNarrowability(inner) => {
                        // The inner type is what could be equal (for == narrowing)
                        // but not always equal (so we don't add to always_equal_union)
                        has_ambiguous = true;
                        narrowed_union = narrowed_union.add(inner);
                    }
                    EqualityResult::EqualityIndicatesPositiveNarrowability(narrowed_element) => {
                        narrowed_union = narrowed_union.add(narrowed_element);
                        always_equal_union = always_equal_union.add(narrowed_element);
                    }
                    EqualityResult::AlwaysUnequal => {
                        has_always_unequal = true;
                    }
                }
            }

            let narrowed = narrowed_union.build();

            // If the narrowed union is empty (Never), it means nothing could compare equal
            if narrowed.is_never() {
                return EqualityResult::AlwaysUnequal;
            }

            // When the union is on the LEFT (being narrowed), we can use the narrowed union
            // for both == and != narrowing.
            // When the union is on the RIGHT (being compared against), and we have a mix of
            // AlwaysEqual and AlwaysUnequal elements, the comparison result depends on which
            // union element is present at runtime. In this case, we should only use the
            // always_equal elements for != narrowing (to be conservative).
            let needs_careful_handling = has_ambiguous
                || (!union_is_left && has_always_unequal && !narrowed.is_never());

            if needs_careful_handling {
                let always_equal = always_equal_union.build();
                if always_equal.is_never() {
                    EqualityResult::Ambiguous
                } else {
                    EqualityResult::InequalityIndicatesNegativeNarrowability(always_equal)
                }
            } else {
                EqualityResult::EqualityIndicatesPositiveNarrowability(narrowed)
            }
        }

        (Type::Intersection(intersection), other) | (other, Type::Intersection(intersection)) => {
            // If we exclude a type that is always equal to other, then the intersection
            // can never equal other. For example: `int & ~Literal[1]` vs `Literal[1]`
            // Since we exclude Literal[1], and Literal[1] == Literal[1] is AlwaysEqual,
            // the intersection can never equal Literal[1].
            if intersection.negative(db).iter().any(|element| {
                equality_special_case(db, *element, other) == EqualityResult::AlwaysEqual
            }) {
                return EqualityResult::AlwaysUnequal;
            }

            // Check positive elements for narrowability
            let mut has_positive_narrowability = false;
            let mut negative_narrowability_type: Option<Type<'db>> = None;

            for element in intersection.positive(db) {
                match equality_special_case(db, *element, other) {
                    EqualityResult::EqualityIndicatesPositiveNarrowability(_) => {
                        has_positive_narrowability = true;
                    }
                    EqualityResult::InequalityIndicatesNegativeNarrowability(ty) => {
                        negative_narrowability_type = Some(ty);
                    }
                    _ => {}
                }
            }

            if has_positive_narrowability {
                EqualityResult::EqualityIndicatesPositiveNarrowability(
                    IntersectionType::from_elements(db, [Type::Intersection(intersection), other]),
                )
            } else if let Some(ty) = negative_narrowability_type {
                EqualityResult::InequalityIndicatesNegativeNarrowability(ty)
            } else {
                EqualityResult::Ambiguous
            }
        }

        (Type::Callable(callable), other) | (other, Type::Callable(callable)) => {
            if callable.is_function_like(db) {
                equality_special_case(db, other, KnownClass::FunctionType.to_instance(db))
            } else {
                EqualityResult::Ambiguous
            }
        }

        (Type::BooleanLiteral(b), other) | (other, Type::BooleanLiteral(b)) => {
            equality_special_case(db, Type::IntLiteral(i64::from(b)), other)
        }

        (Type::IntLiteral(l), Type::IntLiteral(r)) => EqualityResult::from(l == r),

        (Type::BytesLiteral(b1), Type::BytesLiteral(b2)) => EqualityResult::from(b1 == b2),

        (Type::EnumLiteral(l), Type::EnumLiteral(r)) => {
            let left_instance = l.enum_class_instance(db);
            let right_instance = r.enum_class_instance(db);
            let Some(left_equality_semantics) =
                KnownEqualitySemantics::for_final_instance(db, left_instance)
            else {
                return EqualityResult::Ambiguous;
            };
            let Some(right_equality_semantics) =
                KnownEqualitySemantics::for_final_instance(db, right_instance)
            else {
                return EqualityResult::Ambiguous;
            };
            if left_equality_semantics == right_equality_semantics {
                if matches!(
                    left_equality_semantics,
                    KnownEqualitySemantics::Object | KnownEqualitySemantics::Enum
                ) {
                    EqualityResult::from(l == r)
                } else {
                    EqualityResult::from(l.value(db) == r.value(db))
                }
            } else {
                equality_special_case(db, left_instance, right_instance)
            }
        }

        (Type::IntLiteral(int), Type::EnumLiteral(e))
        | (Type::EnumLiteral(e), Type::IntLiteral(int)) => {
            match KnownEqualitySemantics::for_final_instance(db, e.enum_class_instance(db)) {
                Some(KnownEqualitySemantics::Int) => {
                    EqualityResult::from(e.value(db) == Type::IntLiteral(int))
                }
                Some(
                    KnownEqualitySemantics::Bytes
                    | KnownEqualitySemantics::Object
                    | KnownEqualitySemantics::Str
                    | KnownEqualitySemantics::Enum,
                ) => EqualityResult::AlwaysUnequal,
                None => EqualityResult::Ambiguous,
            }
        }

        (Type::BytesLiteral(b), Type::EnumLiteral(e))
        | (Type::EnumLiteral(e), Type::BytesLiteral(b)) => {
            match KnownEqualitySemantics::for_final_instance(db, e.enum_class_instance(db)) {
                Some(KnownEqualitySemantics::Bytes) => {
                    EqualityResult::from(e.value(db) == Type::BytesLiteral(b))
                }
                Some(
                    KnownEqualitySemantics::Int
                    | KnownEqualitySemantics::Object
                    | KnownEqualitySemantics::Str
                    | KnownEqualitySemantics::Enum,
                ) => EqualityResult::AlwaysUnequal,
                None => EqualityResult::Ambiguous,
            }
        }

        (Type::StringLiteral(s), Type::EnumLiteral(e))
        | (Type::EnumLiteral(e), Type::StringLiteral(s)) => {
            match KnownEqualitySemantics::for_final_instance(db, e.enum_class_instance(db)) {
                Some(KnownEqualitySemantics::Str) => {
                    EqualityResult::from(e.value(db) == Type::StringLiteral(s))
                }
                Some(
                    KnownEqualitySemantics::Bytes
                    | KnownEqualitySemantics::Int
                    | KnownEqualitySemantics::Object
                    | KnownEqualitySemantics::Enum,
                ) => EqualityResult::AlwaysUnequal,
                None => EqualityResult::Ambiguous,
            }
        }

        (Type::LiteralString, Type::EnumLiteral(e))
        | (Type::EnumLiteral(e), Type::LiteralString) => {
            match KnownEqualitySemantics::for_final_instance(db, e.enum_class_instance(db)) {
                Some(KnownEqualitySemantics::Str) => {
                    if let Type::StringLiteral(string) = e.value(db) {
                        EqualityResult::EqualityIndicatesPositiveNarrowability(Type::StringLiteral(
                            string,
                        ))
                    } else {
                        EqualityResult::Ambiguous
                    }
                }
                Some(
                    KnownEqualitySemantics::Bytes
                    | KnownEqualitySemantics::Int
                    | KnownEqualitySemantics::Object
                    | KnownEqualitySemantics::Enum,
                ) => EqualityResult::AlwaysUnequal,
                None => EqualityResult::Ambiguous,
            }
        }

        (Type::TypedDict(_), Type::EnumLiteral(e)) | (Type::EnumLiteral(e), Type::TypedDict(_)) => {
            if KnownEqualitySemantics::for_final_instance(db, e.enum_class_instance(db)).is_some() {
                EqualityResult::AlwaysUnequal
            } else {
                EqualityResult::Ambiguous
            }
        }

        (Type::NominalInstance(instance), Type::StringLiteral(s))
        | (Type::StringLiteral(s), Type::NominalInstance(instance)) => {
            if instance.class(db).is_final(db) {
                match KnownEqualitySemantics::for_final_instance(
                    db,
                    Type::NominalInstance(instance),
                ) {
                    Some(KnownEqualitySemantics::Int) | None => EqualityResult::Ambiguous,
                    Some(_) => EqualityResult::AlwaysUnequal,
                }
            } else {
                EqualityResult::InequalityIndicatesNegativeNarrowability(Type::StringLiteral(s))
            }
        }

        (string @ Type::StringLiteral(_), Type::LiteralString)
        | (Type::LiteralString, string @ Type::StringLiteral(_)) => {
            EqualityResult::EqualityIndicatesPositiveNarrowability(string)
        }

        (Type::StringLiteral(_), other) | (other, Type::StringLiteral(_)) => {
            equality_special_case(db, Type::LiteralString, other)
        }

        (Type::LiteralString, Type::LiteralString) => EqualityResult::Ambiguous,

        (Type::DataclassDecorator(_), Type::DataclassDecorator(_)) => EqualityResult::Ambiguous,

        (Type::FunctionLiteral(l), Type::FunctionLiteral(r)) => {
            EqualityResult::from(l.literal(db) == r.literal(db))
        }

        (Type::FunctionLiteral(_) | Type::DataclassDecorator(_), other)
        | (other, Type::FunctionLiteral(_) | Type::DataclassDecorator(_)) => {
            // will unnecessarily return `None` in many instances if `FunctionType` is not `@final`.
            debug_assert!(
                KnownClass::FunctionType
                    .to_class_literal(db)
                    .expect_class_literal()
                    .is_final(db)
            );
            equality_special_case(db, KnownClass::FunctionType.to_instance(db), other)
        }

        (Type::BoundMethod(l), Type::BoundMethod(r)) => {
            if l.function(db).literal(db) != r.function(db).literal(db) {
                EqualityResult::AlwaysUnequal
            } else {
                EqualityResult::Ambiguous
            }
        }

        (Type::BoundMethod(_), other) | (other, Type::BoundMethod(_)) => {
            // will unnecessarily return `None` in many instances if `MethodType` is not `@final`.
            debug_assert!(
                KnownClass::MethodType
                    .to_class_literal(db)
                    .expect_class_literal()
                    .is_final(db)
            );
            equality_special_case(db, KnownClass::MethodType.to_instance(db), other)
        }

        (Type::WrapperDescriptor(l), Type::WrapperDescriptor(r)) => {
            if l == r {
                EqualityResult::AlwaysEqual
            } else {
                EqualityResult::Ambiguous
            }
        }

        (Type::WrapperDescriptor(_), other) | (other, Type::WrapperDescriptor(_)) => {
            // will unnecessarily return `None` in many instances if `WrapperDescriptorType` is not `@final`.
            debug_assert!(
                KnownClass::WrapperDescriptorType
                    .to_class_literal(db)
                    .expect_class_literal()
                    .is_final(db)
            );
            equality_special_case(db, KnownClass::WrapperDescriptorType.to_instance(db), other)
        }

        (Type::BoundSuper(l), Type::BoundSuper(r)) => {
            if l.owner(db) != r.owner(db) && l.pivot_class(db) != r.pivot_class(db) {
                EqualityResult::AlwaysUnequal
            } else {
                EqualityResult::Ambiguous
            }
        }

        // We could do better here but it's unclear if it's worth it.
        // There's no point delegating to `KnownClass::Super.to_instance()`
        // because `super` is not a `@final` class.
        (Type::BoundSuper(_), _) | (_, Type::BoundSuper(_)) => EqualityResult::Ambiguous,

        (Type::SpecialForm(l), Type::SpecialForm(r)) => EqualityResult::from(l == r),

        (Type::SpecialForm(form), other) | (other, Type::SpecialForm(form)) => {
            equality_special_case(db, form.instance_fallback(db), other)
        }

        (Type::ModuleLiteral(l), Type::ModuleLiteral(r)) => {
            EqualityResult::from(l.module(db) == r.module(db))
        }

        // We might be able to do better here in some cases, but it's unclear if it's worth it
        (Type::ModuleLiteral(_), _) | (_, Type::ModuleLiteral(_)) => EqualityResult::Ambiguous,

        (Type::ClassLiteral(l), Type::ClassLiteral(r)) => {
            if KnownEqualitySemantics::for_final_instance(db, l.metaclass_instance_type(db))
                == Some(KnownEqualitySemantics::Object)
            {
                EqualityResult::from(l == r)
            } else {
                EqualityResult::Ambiguous
            }
        }

        // we might be able to do better here after https://github.com/astral-sh/ty/issues/1859 etc. are resolved
        (Type::GenericAlias(_), _) | (_, Type::GenericAlias(_)) => EqualityResult::Ambiguous,

        // Complicated to get right in its entirety (need to recurse into inner variants);
        // unclear if the maintenance effort is worth it
        (Type::KnownBoundMethod(_), Type::KnownBoundMethod(_)) => EqualityResult::Ambiguous,

        // We could do better here too but it's unclear if it's worth it
        (Type::KnownBoundMethod(m), other) | (other, Type::KnownBoundMethod(m)) => {
            // will unnecessarily return `None` in many instances if `WrapperDescriptorType` is not `@final`.
            debug_assert!(
                m.class()
                    .to_class_literal(db)
                    .expect_class_literal()
                    .is_final(db)
            );
            equality_special_case(db, m.class().to_instance(db), other)
        }

        // We could possibly do better for `closed=True` `TypedDict`s?
        (Type::TypedDict(_), Type::TypedDict(_)) => EqualityResult::Ambiguous,

        // We might be able to do better here in some cases, but it's unclear if it's worth it
        (Type::KnownInstance(i), other) | (other, Type::KnownInstance(i)) => {
            equality_special_case(db, i.instance_fallback(db), other)
        }

        // We might be able to do better here in some cases, but it's unclear if it's worth it.
        // There's no point delegating to `KnownClass::property.to_instance()`
        // because `property` is not a `@final` class.
        (Type::PropertyInstance(_), _) | (_, Type::PropertyInstance(_)) => {
            EqualityResult::Ambiguous
        }

        // We should probably do better here,
        // but we need to be careful to respect the difference between instances of `type` and generic-alias instances.
        // We also need to make sure we respect the fact that metaclasses can override `__eq__` and `__ne__`.
        (Type::SubclassOf(_), _) | (_, Type::SubclassOf(_)) => EqualityResult::Ambiguous,

        (
            Type::IntLiteral(_),
            Type::BytesLiteral(_)
            | Type::ClassLiteral(_)
            | Type::TypedDict(_)
            | Type::LiteralString,
        )
        | (
            Type::BytesLiteral(_)
            | Type::ClassLiteral(_)
            | Type::TypedDict(_)
            | Type::LiteralString,
            Type::IntLiteral(_),
        ) => EqualityResult::AlwaysUnequal,

        (
            Type::LiteralString,
            Type::BytesLiteral(_) | Type::ClassLiteral(_) | Type::TypedDict(_),
        )
        | (
            Type::BytesLiteral(_) | Type::ClassLiteral(_) | Type::TypedDict(_),
            Type::LiteralString,
        ) => EqualityResult::AlwaysUnequal,

        (Type::BytesLiteral(_), Type::ClassLiteral(_) | Type::TypedDict(_))
        | (Type::ClassLiteral(_) | Type::TypedDict(_), Type::BytesLiteral(_)) => {
            EqualityResult::AlwaysUnequal
        }

        (Type::ClassLiteral(_), Type::TypedDict(_))
        | (Type::TypedDict(_), Type::ClassLiteral(_)) => EqualityResult::AlwaysUnequal,

        (Type::ClassLiteral(c), other @ (Type::NominalInstance(_) | Type::EnumLiteral(_)))
        | (other @ (Type::NominalInstance(_) | Type::EnumLiteral(_)), Type::ClassLiteral(c)) => {
            equality_special_case(db, c.metaclass_instance_type(db), other)
        }

        (Type::NominalInstance(instance), Type::IntLiteral(i))
        | (Type::IntLiteral(i), Type::NominalInstance(instance)) => {
            let class = instance.class(db);
            if class.is_known(db, KnownClass::Bool) {
                match i {
                    0 | 1 => EqualityResult::EqualityIndicatesPositiveNarrowability(
                        Type::BooleanLiteral(i == 1),
                    ),
                    _ => EqualityResult::AlwaysUnequal,
                }
            } else if class.is_final(db) {
                match KnownEqualitySemantics::for_final_instance(
                    db,
                    Type::NominalInstance(instance),
                ) {
                    Some(KnownEqualitySemantics::Int) | None => EqualityResult::Ambiguous,
                    Some(_) => EqualityResult::AlwaysUnequal,
                }
            } else {
                EqualityResult::InequalityIndicatesNegativeNarrowability(Type::IntLiteral(i))
            }
        }

        (Type::NominalInstance(instance), Type::LiteralString)
        | (Type::LiteralString, Type::NominalInstance(instance)) => {
            let class = instance.class(db);
            if class.is_final(db) {
                match KnownEqualitySemantics::for_final_instance(
                    db,
                    Type::NominalInstance(instance),
                ) {
                    Some(KnownEqualitySemantics::Str) | None => EqualityResult::Ambiguous,
                    Some(_) => EqualityResult::AlwaysUnequal,
                }
            } else {
                EqualityResult::Ambiguous
            }
        }

        (Type::NominalInstance(instance), Type::BytesLiteral(b))
        | (Type::BytesLiteral(b), Type::NominalInstance(instance)) => {
            let class = instance.class(db);
            if class.is_final(db) {
                match KnownEqualitySemantics::for_final_instance(
                    db,
                    Type::NominalInstance(instance),
                ) {
                    Some(KnownEqualitySemantics::Bytes) | None => EqualityResult::Ambiguous,
                    Some(_) => EqualityResult::AlwaysUnequal,
                }
            } else {
                EqualityResult::InequalityIndicatesNegativeNarrowability(Type::BytesLiteral(b))
            }
        }

        (Type::NominalInstance(instance), Type::EnumLiteral(e))
        | (Type::EnumLiteral(e), Type::NominalInstance(instance)) => {
            // Handle bool vs IntEnum
            if instance.has_known_class(db, KnownClass::Bool)
                && KnownEqualitySemantics::for_final_instance(db, Type::EnumLiteral(e))
                    == Some(KnownEqualitySemantics::Int)
            {
                return match e.value(db) {
                    Type::IntLiteral(i @ (0 | 1)) => {
                        EqualityResult::EqualityIndicatesPositiveNarrowability(
                            Type::BooleanLiteral(i == 1),
                        )
                    }
                    Type::IntLiteral(_) => EqualityResult::AlwaysUnequal,
                    _ => EqualityResult::Ambiguous,
                };
            }

            // Check if this is a NominalInstance of an enum class being compared to one of its literals
            let enum_class_literal = instance.class_literal(db);
            let enum_literal_class = e.enum_class(db);
            if enum_class_literal == enum_literal_class {
                // Same enum class - check if it has well-behaved equality
                let enum_instance = e.enum_class_instance(db);
                match KnownEqualitySemantics::for_final_instance(db, enum_instance) {
                    Some(KnownEqualitySemantics::Enum | KnownEqualitySemantics::Object) => {
                        // Standard enum equality - expand to member literals
                        if let Some(member_literals) =
                            enum_member_literals(db, enum_class_literal, None)
                        {
                            let narrowed = UnionType::from_elements(
                                db,
                                member_literals.filter(|member_ty| {
                                    // Keep members that could compare equal to e
                                    !matches!(
                                        equality_special_case(db, *member_ty, Type::EnumLiteral(e)),
                                        EqualityResult::AlwaysUnequal
                                    )
                                }),
                            );
                            return EqualityResult::EqualityIndicatesPositiveNarrowability(narrowed);
                        }
                    }
                    Some(KnownEqualitySemantics::Int) => {
                        // IntEnum - expand to member literals and compare by value
                        if let Some(member_literals) =
                            enum_member_literals(db, enum_class_literal, None)
                        {
                            let narrowed = UnionType::from_elements(
                                db,
                                member_literals.filter(|member_ty| {
                                    !matches!(
                                        equality_special_case(db, *member_ty, Type::EnumLiteral(e)),
                                        EqualityResult::AlwaysUnequal
                                    )
                                }),
                            );
                            return EqualityResult::EqualityIndicatesPositiveNarrowability(narrowed);
                        }
                    }
                    Some(KnownEqualitySemantics::Str | KnownEqualitySemantics::Bytes) => {
                        // StrEnum or BytesEnum - expand to member literals and compare by value
                        if let Some(member_literals) =
                            enum_member_literals(db, enum_class_literal, None)
                        {
                            let narrowed = UnionType::from_elements(
                                db,
                                member_literals.filter(|member_ty| {
                                    !matches!(
                                        equality_special_case(db, *member_ty, Type::EnumLiteral(e)),
                                        EqualityResult::AlwaysUnequal
                                    )
                                }),
                            );
                            return EqualityResult::EqualityIndicatesPositiveNarrowability(narrowed);
                        }
                    }
                    None => {
                        // Custom equality - can't narrow
                        return EqualityResult::Ambiguous;
                    }
                }
            }

            // Different classes or couldn't get member literals - fall back to comparing instances
            equality_special_case(
                db,
                Type::NominalInstance(instance),
                e.enum_class_instance(db),
            )
        }

        // All inhabitants of a `TypedDict` are instances of `dict` at runtime,
        // so there's no point falling back to `KnownClass::Dict.to_instance()` (`dict` is not `@final`!).
        (Type::NominalInstance(_), Type::TypedDict(_))
        | (Type::TypedDict(_), Type::NominalInstance(_)) => EqualityResult::Ambiguous,

        (Type::NominalInstance(l), Type::NominalInstance(r))
            if l == r
                && left.is_singleton(db)
                && KnownEqualitySemantics::for_final_instance(db, left).is_some() =>
        {
            EqualityResult::AlwaysEqual
        }

        (Type::NominalInstance(l), Type::NominalInstance(r)) => {
            let left_class = l.class(db);
            let right_class = r.class(db);
            if left_class.is_final(db) && right_class.is_final(db) {
                let Some(left_equality_semantics) =
                    KnownEqualitySemantics::for_final_instance(db, left)
                else {
                    return EqualityResult::Ambiguous;
                };
                let Some(right_equality_semantics) =
                    KnownEqualitySemantics::for_final_instance(db, right)
                else {
                    return EqualityResult::Ambiguous;
                };
                if (left_equality_semantics != right_equality_semantics
                    || (left_equality_semantics == KnownEqualitySemantics::Object))
                    && left_class.class_literal(db) != right_class.class_literal(db)
                {
                    return EqualityResult::AlwaysUnequal;
                }
            }
            EqualityResult::Ambiguous
        }
    }
}

fn lookup_dunder<'db>(
    db: &'db dyn Db,
    ty: Type<'db>,
    name: &'static str,
) -> PlaceAndQualifiers<'db> {
    ty.member_lookup_with_policy(
        db,
        Name::new_static(name),
        MemberLookupPolicy::MRO_NO_OBJECT_FALLBACK,
    )
}

fn lookup_dunder_eq<'db>(db: &'db dyn Db, ty: Type<'db>) -> PlaceAndQualifiers<'db> {
    lookup_dunder(db, ty, "__eq__")
}

fn lookup_dunder_ne<'db>(db: &'db dyn Db, ty: Type<'db>) -> PlaceAndQualifiers<'db> {
    lookup_dunder(db, ty, "__ne__")
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum KnownEqualitySemantics {
    Object,
    Int,
    Str,
    Bytes,
    /// Standard enum equality (identity-based, like object)
    Enum,
}

impl KnownEqualitySemantics {
    fn for_final_instance<'db>(db: &'db dyn Db, instance: Type<'db>) -> Option<Self> {
        let class = instance.to_meta_type(db);
        let eq = lookup_dunder_eq(db, class);
        let ne = lookup_dunder_ne(db, class);
        if eq.place.is_undefined() && ne.place.is_undefined() {
            return Some(KnownEqualitySemantics::Object);
        }
        let int_class = KnownClass::Int.to_class_literal(db);
        if eq == lookup_dunder_eq(db, int_class) && ne == lookup_dunder_ne(db, int_class) {
            return Some(KnownEqualitySemantics::Int);
        }
        let str_class = KnownClass::Str.to_class_literal(db);
        if eq == lookup_dunder_eq(db, str_class) && ne == lookup_dunder_ne(db, str_class) {
            return Some(KnownEqualitySemantics::Str);
        }
        let bytes_class = KnownClass::Bytes.to_class_literal(db);
        if eq == lookup_dunder_eq(db, bytes_class) && ne == lookup_dunder_ne(db, bytes_class) {
            return Some(KnownEqualitySemantics::Bytes);
        }
        // Check for standard enum equality (identity-based)
        let enum_class = KnownClass::Enum.to_class_literal(db);
        if eq == lookup_dunder_eq(db, enum_class) && ne == lookup_dunder_ne(db, enum_class) {
            return Some(KnownEqualitySemantics::Enum);
        }
        None
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum EqualityResult<'db> {
    /// The two types always compare equal.
    ///
    /// This does not necessarily indicate anything about whether the two types are
    /// the same type, or even whether they have any subtyping/assignability relationship!
    /// For example, an object of type `Literal[1]` will always compare equal to an object
    /// of type `Literal[Foo.X]` in the following example, despite the fact that `Literal[1]`
    /// is *disjoint* from `Literal[Foo.X]`:
    ///
    /// ```py
    /// from enum import IntEnum
    ///
    /// class Foo(IntEnum):
    ///     X = 1
    /// ```
    AlwaysEqual,

    /// Equality between the two types indicates that both sides can be narrowed to the
    /// wrapped type.
    ///
    /// For example, if an object of type `LiteralString` compares equal to an object of type
    /// `Literal["foo"]`, we can safely narrow the type of both operands to `Literal["foo"]`.
    EqualityIndicatesPositiveNarrowability(Type<'db>),

    /// The two types may compare equal or unequal, depending on runtime values.
    Ambiguous,

    InequalityIndicatesNegativeNarrowability(Type<'db>),

    /// The two types always compare unequal.
    ///
    /// Similar to [`AlwaysEqual`], this does not necessarily indicate anything about
    /// whether the two types are disjoint!
    AlwaysUnequal,
}

impl From<bool> for EqualityResult<'_> {
    fn from(value: bool) -> Self {
        if value {
            EqualityResult::AlwaysEqual
        } else {
            EqualityResult::AlwaysUnequal
        }
    }
}
