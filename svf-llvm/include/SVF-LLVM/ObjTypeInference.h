//===- ObjTypeInference.h -- Type inference----------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//
//
//===----------------------------------------------------------------------===//

#ifndef SVF_OBJTYPEINFERENCE_H
#define SVF_OBJTYPEINFERENCE_H

#include "Util/SVFUtil.h"
#include "SVF-LLVM/BasicTypes.h"

namespace SVF
{

class ObjTypeInference
{
public:
    typedef Set<const Value*> ValueSet;
    typedef Map<const Value*, ValueSet> ValueToValueSet;
    typedef Map<const Value*, const Type*> ValueToType;
    typedef std::pair<const Value*, bool> ValueBoolPair;

    explicit ObjTypeInference() = default;
    ~ObjTypeInference() = default;

    /// Get or infer the type of the object pointed by `var`.
    const Type* inferObjType(const Value* var);

    /// Default type used when inference cannot decide.
    const Type* defaultType(const Value* val);

private:
    /// Forward infer object type from a value.
    const Type* fwInferObjType(const Value* var);
    /// Backward collect possible allocations of a value.
    Set<const Value*>& bwfindAllocOfVar(const Value* var);
    /// Whether value is an allocation-like object.
    bool isAlloc(const Value* val);
    /// Pick a conservative representative type.
    const Type* selectConservativeType(Set<const Type*>& objTys);

private:
    ValueToValueSet valueToInferSites;
    ValueToType valueToType;
    ValueToValueSet valueToAllocs;
};

} // namespace SVF

#endif // SVF_OBJTYPEINFERENCE_H
