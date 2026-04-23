//===- ObjTypeInference.cpp -- Type inference----------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//
//
//===----------------------------------------------------------------------===//

#include "SVF-LLVM/ObjTypeInference.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "Util/WorkList.h"

using namespace SVF;
using namespace SVFUtil;
using namespace LLVMUtil;

namespace
{
static const Type* inferSiteToType(const Value* val)
{
    assert(val && "value cannot be null");
    if (SVFUtil::isa<LoadInst, StoreInst>(val))
    {
        return llvm::getLoadStoreType(const_cast<Value*>(val));
    }
    if (const auto* gepInst = SVFUtil::dyn_cast<GetElementPtrInst>(val))
    {
        return gepInst->getSourceElementType();
    }
    if (const auto* call = SVFUtil::dyn_cast<CallBase>(val))
    {
        return call->getFunctionType();
    }
    if (const auto* allocaInst = SVFUtil::dyn_cast<AllocaInst>(val))
    {
        return allocaInst->getAllocatedType();
    }
    if (const auto* globalValue = SVFUtil::dyn_cast<GlobalValue>(val))
    {
        return globalValue->getValueType();
    }
    return nullptr;
}
}

const Type* ObjTypeInference::defaultType(const Value* val)
{
    assert(val && "val cannot be null");
    // Conservative default for unresolved pointer objects.
    // NOTE: Avoid querying SVF callsite mapping here because this function can
    // run before instruction-to-SVF mapping is fully initialized.
    return PointerType::getUnqual(LLVMModuleSet::getLLVMModuleSet()->getContext());
}

const Type* ObjTypeInference::selectConservativeType(Set<const Type*>& objTys)
{
    if (objTys.empty())
        return nullptr;
    // Keep deterministic behavior; pick first inferred type.
    return *objTys.begin();
}

const Type* ObjTypeInference::inferObjType(const Value* var)
{
    // Temporary conservative mode for stability on opaque-pointer migration.
    // We avoid complex forward/backward traversal here because it may touch
    // values whose SVF mapping has not been fully initialized yet.
    (void)var;
    return defaultType(var);
}

const Type* ObjTypeInference::fwInferObjType(const Value* var)
{
    auto it = valueToType.find(var);
    if (it != valueToType.end())
        return it->second ? it->second : defaultType(var);

    FILOWorkList<ValueBoolPair> workList;
    Set<ValueBoolPair> visited;
    workList.push({var, false});

    while (!workList.empty())
    {
        auto cur = workList.pop();
        if (visited.count(cur))
            continue;
        visited.insert(cur);

        const Value* curValue = cur.first;
        bool canUpdate = cur.second;
        Set<const Value*> inferSites;

        auto insertInferSite = [&inferSites, &canUpdate](const Value* inferSite)
        {
            if (canUpdate)
                inferSites.insert(inferSite);
        };

        auto insertOrPush = [this, &workList, &inferSites, &canUpdate](const Value* next)
        {
            auto nextIt = valueToInferSites.find(next);
            if (canUpdate)
            {
                if (nextIt != valueToInferSites.end())
                    inferSites.insert(nextIt->second.begin(), nextIt->second.end());
            }
            else if (nextIt == valueToInferSites.end())
            {
                workList.push({next, false});
            }
        };

        if (!canUpdate && !valueToInferSites.count(curValue))
            workList.push({curValue, true});

        if (const auto* gepInst = SVFUtil::dyn_cast<GetElementPtrInst>(curValue))
            insertInferSite(gepInst);

        for (const auto& user : curValue->users())
        {
            if (const auto* loadInst = SVFUtil::dyn_cast<LoadInst>(user))
            {
                insertInferSite(loadInst);
            }
            else if (const auto* storeInst = SVFUtil::dyn_cast<StoreInst>(user))
            {
                if (storeInst->getPointerOperand() == curValue)
                    insertInferSite(storeInst);
            }
            else if (const auto* bitcast = SVFUtil::dyn_cast<BitCastInst>(user))
            {
                insertOrPush(bitcast);
            }
            else if (const auto* phiNode = SVFUtil::dyn_cast<PHINode>(user))
            {
                insertOrPush(phiNode);
            }
            else if (const auto* callBase = SVFUtil::dyn_cast<CallBase>(user))
            {
                if (SVFUtil::isa<Function>(curValue) && curValue == callBase->getCalledFunction())
                    continue;
                if (callBase->hasArgument(curValue))
                {
                    if (const Function* callee = callBase->getCalledFunction())
                    {
                        if (!callee->isDeclaration() && !callee->isVarArg())
                        {
                            auto itArg = std::find(callBase->arg_begin(), callBase->arg_end(), curValue);
                            if (itArg != callBase->arg_end())
                            {
                                u32_t pos = std::distance(callBase->arg_begin(), itArg);
                                insertOrPush(callee->getArg(pos));
                            }
                        }
                    }
                }
            }
        }

        if (canUpdate)
        {
            Set<const Type*> inferredTypes;
            for (const Value* site : inferSites)
            {
                if (const Type* t = inferSiteToType(site))
                    inferredTypes.insert(t);
            }
            valueToInferSites[curValue] = SVFUtil::move(inferSites);
            valueToType[curValue] = selectConservativeType(inferredTypes);
        }
    }

    const Type* ty = valueToType[var];
    return ty ? ty : defaultType(var);
}

Set<const Value*>& ObjTypeInference::bwfindAllocOfVar(const Value* var)
{
    auto it = valueToAllocs.find(var);
    if (it != valueToAllocs.end())
        return it->second;

    FILOWorkList<ValueBoolPair> workList;
    Set<ValueBoolPair> visited;
    workList.push({var, false});

    while (!workList.empty())
    {
        auto cur = workList.pop();
        if (visited.count(cur))
            continue;
        visited.insert(cur);

        const Value* curValue = cur.first;
        bool canUpdate = cur.second;
        Set<const Value*> sources;

        auto insertSource = [&sources, &canUpdate](const Value* source)
        {
            if (canUpdate)
                sources.insert(source);
        };

        auto insertOrPush = [this, &sources, &workList, &canUpdate](const Value* next)
        {
            auto nextIt = valueToAllocs.find(next);
            if (canUpdate)
            {
                if (nextIt != valueToAllocs.end())
                    sources.insert(nextIt->second.begin(), nextIt->second.end());
            }
            else if (nextIt == valueToAllocs.end())
            {
                workList.push({next, false});
            }
        };

        if (!canUpdate && !valueToAllocs.count(curValue))
            workList.push({curValue, true});

        if (isAlloc(curValue))
        {
            insertSource(curValue);
        }
        else if (const auto* bitcast = SVFUtil::dyn_cast<BitCastInst>(curValue))
        {
            insertOrPush(bitcast->getOperand(0));
        }
        else if (const auto* phiNode = SVFUtil::dyn_cast<PHINode>(curValue))
        {
            for (u32_t i = 0; i < phiNode->getNumOperands(); ++i)
                insertOrPush(phiNode->getOperand(i));
        }

        if (canUpdate)
            valueToAllocs[curValue] = SVFUtil::move(sources);
    }

    return valueToAllocs[var];
}

bool ObjTypeInference::isAlloc(const Value* val)
{
    return LLVMUtil::isObject(val);
}
