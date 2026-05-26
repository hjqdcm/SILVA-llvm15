//===- SymbolTableBuilder.cpp -- Symbol Table builder---------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

/*
 * SymbolTableBuilder.cpp
 *
 *  Created on: Apr 28, 2014
 *      Author: Yulei Sui
 */

#include <memory>

#include "SVF-LLVM/SymbolTableBuilder.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "Util/NodeIDAllocator.h"
#include "Util/Options.h"
#include "SVFIR/SVFModule.h"
#include "Util/SVFUtil.h"
#include "SVF-LLVM/BasicTypes.h"
#include "SVF-LLVM/ObjTypeInference.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "Util/CppUtil.h"
#include "SVF-LLVM/GEPTypeBridgeIterator.h" // include bridge_gep_iterator

using namespace SVF;
using namespace SVFUtil;
using namespace LLVMUtil;

MemObj* SymbolTableBuilder::createBlkObj(SymID symId)
{
    assert(symInfo->isBlkObj(symId));
    assert(symInfo->objMap.find(symId)==symInfo->objMap.end());
    LLVMModuleSet* llvmset = LLVMModuleSet::getLLVMModuleSet();
    MemObj* obj =
        new MemObj(symId, symInfo->createObjTypeInfo(llvmset->getSVFType(
                       IntegerType::get(llvmset->getContext(), 32))));
    symInfo->objMap[symId] = obj;
    return obj;
}

MemObj* SymbolTableBuilder::createConstantObj(SymID symId)
{
    assert(symInfo->isConstantObj(symId));
    assert(symInfo->objMap.find(symId)==symInfo->objMap.end());
    LLVMModuleSet* llvmset = LLVMModuleSet::getLLVMModuleSet();
    MemObj* obj =
        new MemObj(symId, symInfo->createObjTypeInfo(llvmset->getSVFType(
                       IntegerType::get(llvmset->getContext(), 32))));
    symInfo->objMap[symId] = obj;
    return obj;
}


/*!
 *  This method identify which is value sym and which is object sym
 */
void SymbolTableBuilder::buildMemModel(SVFModule* svfModule)
{
    SVFUtil::increaseStackSize();

    symInfo->setModule(svfModule);

    // Pointer #0 always represents the null pointer.
    assert(symInfo->totalSymNum++ == SymbolTableInfo::NullPtr && "Something changed!");

    // Pointer #1 always represents the pointer points-to black hole.
    assert(symInfo->totalSymNum++ == SymbolTableInfo::BlkPtr && "Something changed!");

    // Object #2 is black hole the object that may point to any object
    assert(symInfo->totalSymNum++ == SymbolTableInfo::BlackHole && "Something changed!");
    createBlkObj(SymbolTableInfo::BlackHole);

    // Object #3 always represents the unique constant of a program (merging all constants if Options::ModelConsts is disabled)
    assert(symInfo->totalSymNum++ == SymbolTableInfo::ConstantObj && "Something changed!");
    createConstantObj(SymbolTableInfo::ConstantObj);

    for (Module &M : LLVMModuleSet::getLLVMModuleSet()->getLLVMModules())
    {
        // Add symbols for all the globals .
        for (const GlobalVariable& gv : M.globals())
        {
            collectSym(&gv);
        }

        // Add symbols for all the global aliases
        for (const GlobalAlias& ga : M.aliases())
        {
            collectSym(&ga);
            collectSym(ga.getAliasee());
        }

        // Add symbols for all of the functions and the instructions in them.
        for (const Function& fun : M.functions())
        {
            collectSym(&fun);
            collectRet(&fun);
            if (fun.getFunctionType()->isVarArg())
                collectVararg(&fun);

            // Add symbols for all formal parameters.
            for (const Argument& arg : fun.args())
            {
                collectSym(&arg);
            }

            // collect and create symbols inside the function body
            for (const Instruction& inst : instructions(fun))
            {
                collectSym(&inst);

                // initialization for some special instructions
                //{@
                if (const StoreInst* st = SVFUtil::dyn_cast<StoreInst>(&inst))
                {
                    collectSym(st->getPointerOperand());
                    collectSym(st->getValueOperand());
                }
                else if (const LoadInst* ld =
                             SVFUtil::dyn_cast<LoadInst>(&inst))
                {
                    collectSym(ld->getPointerOperand());
                }
                else if (const AllocaInst* alloc =
                             SVFUtil::dyn_cast<AllocaInst>(&inst))
                {
                    collectSym(alloc->getArraySize());
                }
                else if (const PHINode* phi = SVFUtil::dyn_cast<PHINode>(&inst))
                {
                    for (u32_t i = 0; i < phi->getNumIncomingValues(); ++i)
                    {
                        collectSym(phi->getIncomingValue(i));
                    }
                }
                else if (const GetElementPtrInst* gep =
                             SVFUtil::dyn_cast<GetElementPtrInst>(&inst))
                {
                    collectSym(gep->getPointerOperand());
                    for (u32_t i = 0; i < gep->getNumOperands(); ++i)
                    {
                        collectSym(gep->getOperand(i));
                    }
                }
                else if (const SelectInst* sel =
                             SVFUtil::dyn_cast<SelectInst>(&inst))
                {
                    collectSym(sel->getTrueValue());
                    collectSym(sel->getFalseValue());
                    collectSym(sel->getCondition());
                }
                else if (const BinaryOperator* binary =
                             SVFUtil::dyn_cast<BinaryOperator>(&inst))
                {
                    for (u32_t i = 0; i < binary->getNumOperands(); i++)
                        collectSym(binary->getOperand(i));
                }
                else if (const UnaryOperator* unary =
                             SVFUtil::dyn_cast<UnaryOperator>(&inst))
                {
                    for (u32_t i = 0; i < unary->getNumOperands(); i++)
                        collectSym(unary->getOperand(i));
                }
                else if (const CmpInst* cmp = SVFUtil::dyn_cast<CmpInst>(&inst))
                {
                    for (u32_t i = 0; i < cmp->getNumOperands(); i++)
                        collectSym(cmp->getOperand(i));
                }
                else if (const CastInst* cast =
                             SVFUtil::dyn_cast<CastInst>(&inst))
                {
                    collectSym(cast->getOperand(0));
                }
                else if (const ReturnInst* ret =
                             SVFUtil::dyn_cast<ReturnInst>(&inst))
                {
                    if (ret->getReturnValue())
                        collectSym(ret->getReturnValue());
                }
                else if (const BranchInst* br =
                             SVFUtil::dyn_cast<BranchInst>(&inst))
                {
                    Value* opnd = br->isConditional() ? br->getCondition() : br->getOperand(0);
                    collectSym(opnd);
                }
                else if (const SwitchInst* sw =
                             SVFUtil::dyn_cast<SwitchInst>(&inst))
                {
                    collectSym(sw->getCondition());
                }
                else if (isNonInstricCallSite(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(&inst)))
                {

                    const CallBase* cs = LLVMUtil::getLLVMCallSite(&inst);
                    for (u32_t i = 0; i < cs->arg_size(); i++)
                    {
                        collectSym(cs->getArgOperand(i));
                    }
                    // Calls to inline asm need to be added as well because the
                    // callee isn't referenced anywhere else.
                    const Value* Callee = cs->getCalledOperand();
                    collectSym(Callee);

                    // TODO handle inlineAsm
                    /// if (SVFUtil::isa<InlineAsm>(Callee))
                }
                //@}
            }
        }
    }

    symInfo->totalSymNum = NodeIDAllocator::get()->endSymbolAllocation();
    if (Options::SymTabPrint())
    {
        symInfo->dump();
    }
}

void SymbolTableBuilder::collectSVFTypeInfo(const Value* val)
{
    (void)getOrAddSVFTypeInfo(val->getType());
    if (const PointerType * ptrType = SVFUtil::dyn_cast<PointerType>(val->getType()))
    {
        const Type* objtype = LLVMUtil::getPtrElementType(ptrType);
        (void)getOrAddSVFTypeInfo(objtype);
    }
    if(isGepConstantExpr(val) || SVFUtil::isa<GetElementPtrInst>(val))
    {
        for (bridge_gep_iterator
                gi = bridge_gep_begin(SVFUtil::cast<User>(val)),
                ge = bridge_gep_end(SVFUtil::cast<User>(val));
                gi != ge; ++gi)
        {
            const Type* gepTy = *gi;
            (void)getOrAddSVFTypeInfo(gepTy);
        }
    }
}

/*!
 * Collect symbols, including value and object syms
 */
void SymbolTableBuilder::collectSym(const Value* val)
{

    //TODO: filter the non-pointer type // if (!SVFUtil::isa<PointerType>(val->getType()))  return;

    DBOUT(DMemModel,
          outs()
          << "collect sym from ##"
          << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val)->toString()
          << " \n");
    //TODO handle constant expression value here??
    handleCE(val);

    // create a value sym
    collectVal(val);

    collectSVFTypeInfo(val);
    collectSVFTypeInfo(LLVMUtil::getGlobalRep(val));

    // create an object If it is a heap, stack, global, function.
    if (isObject(val))
    {
        collectObj(val);
    }
}

/*!
 * Get value sym, if not available create a new one
 */
void SymbolTableBuilder::collectVal(const Value* val)
{
    // collect and record special sym here
    if (LLVMUtil::isNullPtrSym(val) || LLVMUtil::isBlackholeSym(val))
    {
        return;
    }
    SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
    if (svfVal == nullptr)
        return;

    SymbolTableInfo::ValueToIDMapTy::iterator iter = symInfo->valSymMap.find(svfVal);
    if (iter == symInfo->valSymMap.end())
    {
        // create val sym and sym type
        SymID id = NodeIDAllocator::get()->allocateValueId();
        symInfo->valSymMap.insert(std::make_pair(svfVal, id));
        DBOUT(DMemModel,
              outs() << "create a new value sym " << id << "\n");
        ///  handle global constant expression here
        if (const GlobalVariable* globalVar = SVFUtil::dyn_cast<GlobalVariable>(val))
            handleGlobalCE(globalVar);
    }

    if (isConstantObjSym(val))
        collectObj(val);
}

/*!
 * Get memory object sym, if not available create a new one
 */
void SymbolTableBuilder::collectObj(const Value* val)
{
    val = LLVMUtil::getGlobalRep(val);
    SymbolTableInfo::ValueToIDMapTy::iterator iter = symInfo->objSymMap.find(
                LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val));
    if (iter == symInfo->objSymMap.end())
    {
        SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
        // if the object pointed by the pointer is a constant data (e.g., i32 0) or a global constant object (e.g. string)
        // then we treat them as one ConstantObj
        if (isConstantObjSym(val) && !symInfo->getModelConstants())
        {
            symInfo->objSymMap.insert(std::make_pair(svfVal, symInfo->constantSymID()));
        }
        // otherwise, we will create an object for each abstract memory location
        else
        {
            // create obj sym and sym type
            SymID id = NodeIDAllocator::get()->allocateObjectId();
            symInfo->objSymMap.insert(std::make_pair(svfVal, id));
            DBOUT(DMemModel,
                  outs() << "create a new obj sym " << id << "\n");

            // create a memory object
            MemObj* mem =
                new MemObj(id, createObjTypeInfo(val),
                           LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val));
            assert(symInfo->objMap.find(id) == symInfo->objMap.end());
            symInfo->objMap[id] = mem;
        }
    }
}

/*!
 * Create unique return sym, if not available create a new one
 */
void SymbolTableBuilder::collectRet(const Function* val)
{
    const SVFFunction* svffun =
        LLVMModuleSet::getLLVMModuleSet()->getSVFFunction(val);
    SymbolTableInfo::FunToIDMapTy::iterator iter =
        symInfo->returnSymMap.find(svffun);
    if (iter == symInfo->returnSymMap.end())
    {
        SymID id = NodeIDAllocator::get()->allocateValueId();
        symInfo->returnSymMap.insert(std::make_pair(svffun, id));
        DBOUT(DMemModel, outs() << "create a return sym " << id << "\n");
    }
}

/*!
 * Create vararg sym, if not available create a new one
 */
void SymbolTableBuilder::collectVararg(const Function* val)
{
    const SVFFunction* svffun =
        LLVMModuleSet::getLLVMModuleSet()->getSVFFunction(val);
    SymbolTableInfo::FunToIDMapTy::iterator iter =
        symInfo->varargSymMap.find(svffun);
    if (iter == symInfo->varargSymMap.end())
    {
        SymID id = NodeIDAllocator::get()->allocateValueId();
        symInfo->varargSymMap.insert(std::make_pair(svffun, id));
        DBOUT(DMemModel, outs() << "create a vararg sym " << id << "\n");
    }
}

/*!
 * Handle constant expression
 */
void SymbolTableBuilder::handleCE(const Value* val)
{
    if (!LLVMUtil::isPlausibleLLVMValuePointer(val))
        return;
    if (const Constant* ref = SVFUtil::dyn_cast<Constant>(val))
    {
        if (const ConstantExpr* ce = isGepConstantExpr(ref))
        {
            DBOUT(DMemModelCE, outs() << "handle constant expression "
                  << LLVMModuleSet::getLLVMModuleSet()
                  ->getSVFValue(ref)
                  ->toString()
                  << "\n");
            collectVal(ce);

            // handle the recursive constant express case
            // like (gep (bitcast (gep X 1)) 1); the inner gep is ce->getOperand(0)
            for (u32_t i = 0; i < ce->getNumOperands(); ++i)
            {
                const Value* op = ce->getOperand(i);
                if (!LLVMUtil::isPlausibleLLVMValuePointer(op))
                    continue;
                collectVal(op);
                handleCE(op);
            }
        }
        else if (const ConstantExpr* ce = isCastConstantExpr(ref))
        {
            DBOUT(DMemModelCE, outs() << "handle constant expression "
                  << LLVMModuleSet::getLLVMModuleSet()
                  ->getSVFValue(ref)
                  ->toString()
                  << "\n");
            collectVal(ce);
            {
                const Value* op0 = ce->getOperand(0);
                if (LLVMUtil::isPlausibleLLVMValuePointer(op0))
                {
                    collectVal(op0);
                    // handle the recursive constant express case
                    // like (gep (bitcast (gep X 1)) 1); the inner gep is ce->getOperand(0)
                    handleCE(op0);
                }
            }
        }
        else if (const ConstantExpr* ce = isSelectConstantExpr(ref))
        {
            DBOUT(DMemModelCE, outs() << "handle constant expression "
                  << LLVMModuleSet::getLLVMModuleSet()
                  ->getSVFValue(ref)
                  ->toString()
                  << "\n");
            collectVal(ce);
            for (u32_t si = 0; si < 3u; ++si)
            {
                const Value* sop = ce->getOperand(si);
                if (LLVMUtil::isPlausibleLLVMValuePointer(sop))
                    collectVal(sop);
            }
            // handle the recursive constant express case
            // like (gep (bitcast (gep X 1)) 1); the inner gep is ce->getOperand(0)
            for (u32_t si = 0; si < 3u; ++si)
            {
                const Value* sop = ce->getOperand(si);
                if (LLVMUtil::isPlausibleLLVMValuePointer(sop))
                    handleCE(sop);
            }
        }
        // if we meet a int2ptr, then it points-to black hole
        else if (const ConstantExpr* int2Ptrce = isInt2PtrConstantExpr(ref))
        {
            collectVal(int2Ptrce);
        }
        else if (const ConstantExpr* ptr2Intce = isPtr2IntConstantExpr(ref))
        {
            collectVal(ptr2Intce);
            const Constant* opnd = ptr2Intce->getOperand(0);
            if (LLVMUtil::isPlausibleLLVMValuePointer(opnd))
                handleCE(opnd);
        }
        else if (isTruncConstantExpr(ref) || isCmpConstantExpr(ref))
        {
            collectVal(ref);
        }
        else if (isBinaryConstantExpr(ref))
        {
            collectVal(ref);
        }
        else if (isUnaryConstantExpr(ref))
        {
            // we don't handle unary constant expression like fneg(x) now
            collectVal(ref);
        }
        else if (SVFUtil::isa<ConstantAggregate>(ref))
        {
            // we don't handle constant aggregate like constant vectors
            collectVal(ref);
        }
        else if (const ConstantExpr* ce = SVFUtil::dyn_cast<ConstantExpr>(ref))
        {
            // e.g. addrspacecast (not covered by isCastConstantExpr which only matches bitcast),
            // freeze, or other CE opcodes: conservatively collect operands for the symbol table.
            collectVal(ce);
            for (u32_t i = 0, e = ce->getNumOperands(); i != e; ++i)
            {
                const Value* op = ce->getOperand(i);
                if (!LLVMUtil::isPlausibleLLVMValuePointer(op))
                    continue;
                collectVal(op);
                handleCE(op);
            }
        }
        else
        {
            //assert(!SVFUtil::isa<ConstantExpr>(val) &&
                   //"we don't handle all other constant expression for now!");
            collectVal(ref);
        }
    }
}

/*!
 * Handle global constant expression
 */
void SymbolTableBuilder::handleGlobalCE(const GlobalVariable* G)
{
    assert(G);

    //The type this global points to
    const Type* T = G->getValueType();
    bool is_array = false;
    if (!LLVMUtil::isPlausibleLLVMTypePointer(T))
    {
        if (G->hasInitializer())
            handleGlobalInitializerCE(G->getInitializer());
        return;
    }
    // An array is considered a single variable of its type.
    while (true)
    {
        const ArrayType* AT = SVFUtil::dyn_cast<ArrayType>(T);
        if (!AT)
            break;
        const Type* elem = AT->getElementType();
        if (!LLVMUtil::isPlausibleLLVMTypePointer(elem))
            break;
        T = elem;
        is_array = true;
    }

    if (LLVMUtil::isPlausibleLLVMTypePointer(T) && SVFUtil::isa<StructType>(T))
    {
        //A struct may be used in constant GEP expr.
        for (const User* user : G->users())
        {
            handleCE(user);
        }
    }
    else if (is_array)
    {
        for (const User* user : G->users())
        {
            handleCE(user);
        }
    }

    if (G->hasInitializer())
    {
        handleGlobalInitializerCE(G->getInitializer());
    }
}

/*!
 * Handle global variable initialization
 */
void SymbolTableBuilder::handleGlobalInitializerCE(const Constant* C)
{
    if (C == nullptr)
        return;
    if (!LLVMUtil::isPlausibleLLVMValuePointer(C))
        return;
    const Type* cTy = C->getType();
    if (!LLVMUtil::isPlausibleLLVMTypePointer(cTy))
        return;

    if (SVFUtil::isa<Function>(C))
        return;

    // In opaque-pointer mode, avoid querying type eagerly here.
    if (SVFUtil::isa<ConstantArray>(C))
    {
        const ArrayType* AT = SVFUtil::dyn_cast<ArrayType>(cTy);
        const unsigned nOps = C->getNumOperands();
        // If the aggregate layout disagrees with the type, operand Uses can be
        // corrupt; getOperand(0) may SIGSEGV inside llvm::Use (see core stacks).
        const bool layoutOk =
            AT && LLVMUtil::isPlausibleLLVMTypePointer(AT) &&
            AT->getNumElements() == static_cast<uint64_t>(nOps);
        if (layoutOk)
        {
            for (u32_t i = 0; i != nOps; ++i)
            {
                const Value* opv = C->getOperand(i);
                if (!LLVMUtil::isPlausibleLLVMValuePointer(opv))
                    continue;
                if (const Constant* op = SVFUtil::dyn_cast<Constant>(opv))
                    handleGlobalInitializerCE(op);
            }
        }
    }
    else if (SVFUtil::isa<ConstantStruct>(C))
    {
        const StructType* ST = SVFUtil::dyn_cast<StructType>(cTy);
        const unsigned nOps = C->getNumOperands();
        const bool layoutOk =
            ST && LLVMUtil::isPlausibleLLVMTypePointer(ST) &&
            static_cast<uint64_t>(ST->getNumElements()) ==
                static_cast<uint64_t>(nOps);
        if (layoutOk)
        {
            for (u32_t i = 0; i != nOps; ++i)
            {
                const Value* opv = C->getOperand(i);
                if (!LLVMUtil::isPlausibleLLVMValuePointer(opv))
                    continue;
                if (const Constant* op = SVFUtil::dyn_cast<Constant>(opv))
                    handleGlobalInitializerCE(op);
            }
        }
    }
    else if(const ConstantData* data = SVFUtil::dyn_cast<ConstantData>(C))
    {
        if (Options::ModelConsts())
        {
            if (const ConstantDataSequential* seq =
                        SVFUtil::dyn_cast<ConstantDataSequential>(data))
            {
                for(u32_t i = 0; i < seq->getNumElements(); i++)
                {
                    const Constant* ct = seq->getElementAsConstant(i);
                    handleGlobalInitializerCE(ct);
                }
            }
            else
            {
                assert(
                    (SVFUtil::isa<ConstantAggregateZero, UndefValue>(data)) &&
                    "Single value type data should have been handled!");
            }
        }
    }
    else if (const ConstantExpr* E = SVFUtil::dyn_cast<ConstantExpr>(C))
    {
        handleCE(E);
    }
    else if (cTy->isSingleValueType())
    {
        collectVal(C);
    }
    else
    {
        //TODO:assert(SVFUtil::isa<ConstantVector>(C),"what else do we have");
    }
}

/*
 * Initial the memory object here
 */
ObjTypeInfo* SymbolTableBuilder::createObjTypeInfo(const Value* val)
{
    const PointerType* refTy = nullptr;
    LLVMModuleSet* llvmModuleSet = LLVMModuleSet::getLLVMModuleSet();
    ObjTypeInference* typeInference = llvmModuleSet->getTypeInference();

    const Instruction* I = SVFUtil::dyn_cast<Instruction>(val);

    // We consider two types of objects:
    // (1) A heap/static object from a callsite
    if (I && isNonInstricCallSite(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(I)))
    {
        refTy = getRefTypeOfHeapAllocOrStatic(I);
    }
    // (2) Other objects (e.g., alloca, global, etc.)
    else
        refTy = SVFUtil::dyn_cast<PointerType>(val->getType());

    if (refTy)
    {
        Type* objTy = nullptr;
        // In opaque-pointer mode, pointee type can be missing. Prefer inferred type.
        if (typeInference)
        {
            objTy = const_cast<Type*>(typeInference->inferObjType(val));
        }
        if (objTy == nullptr)
        {
            objTy = getPtrElementType(refTy);
        }
        ObjTypeInfo* typeInfo = new ObjTypeInfo(
            llvmModuleSet->getSVFType(objTy),
            Options::MaxFieldLimit());
        initTypeInfo(typeInfo,val, objTy);
        return typeInfo;
    }
    else
    {
        writeWrnMsg("try to create an object with a non-pointer type.");
        writeWrnMsg(val->getName().str());
        writeWrnMsg("(" + LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val)->getSourceLoc() + ")");
        if (isConstantObjSym(val))
        {
            ObjTypeInfo* typeInfo = new ObjTypeInfo(
                LLVMModuleSet::getLLVMModuleSet()->getSVFType(val->getType()),
                0);
            initTypeInfo(typeInfo,val, val->getType());
            return typeInfo;
        }
        else
        {
            assert(false && "Memory object must be either (1) held by a pointer-typed ref value or (2) a constant value (e.g., 10).");
            abort();
        }
    }
}

/*!
 * Analyse types of all flattened fields of this object
 */
void SymbolTableBuilder::analyzeObjType(ObjTypeInfo* typeinfo, const Value* val,
                                        const Type* objLayoutTy)
{

    const PointerType* refty = SVFUtil::dyn_cast<PointerType>(val->getType());
    assert(refty && "this value should be a pointer type!");
    Type* elemTy = nullptr;
    // In opaque-pointer IR, getPtrElementType(refTy) is often i8. For `alloca ptr`
    // createObjTypeInfo passes the allocated type (opaque ptr); that is still the
    // correct logical layout for a pointer-sized slot — do not downgrade to i8.
    if (objLayoutTy)
        elemTy = const_cast<Type*>(objLayoutTy);
    else
        elemTy = getPtrElementType(refty);
    bool isPtrObj = false;
    if (!LLVMUtil::isPlausibleLLVMTypePointer(elemTy))
        return;
    // Find the inter nested array element
    while (true)
    {
        const ArrayType* AT = SVFUtil::dyn_cast<ArrayType>(elemTy);
        if (!AT)
            break;
        Type* next = const_cast<Type*>(AT->getElementType());
        if (!LLVMUtil::isPlausibleLLVMTypePointer(next))
            break;
        elemTy = next;
        if (elemTy->isPointerTy())
            isPtrObj = true;
        if (SVFUtil::isa<GlobalVariable>(val) &&
                SVFUtil::cast<GlobalVariable>(val)->hasInitializer() &&
                SVFUtil::isa<ConstantArray>(
                    SVFUtil::cast<GlobalVariable>(val)->getInitializer()))
            typeinfo->setFlag(ObjTypeInfo::CONST_ARRAY_OBJ);
        else
            typeinfo->setFlag(ObjTypeInfo::VAR_ARRAY_OBJ);
    }
    if (!LLVMUtil::isPlausibleLLVMTypePointer(elemTy))
        return;
    if (const StructType* ST = SVFUtil::dyn_cast<StructType>(elemTy))
    {
        const std::vector<const SVFType*>& flattenFields =
            getOrAddSVFTypeInfo(ST)->getFlattenFieldTypes();
        isPtrObj |= std::any_of(flattenFields.begin(), flattenFields.end(),
                                [](const SVFType* ty)
        {
            return ty->isPointerTy();
        });
        if (SVFUtil::isa<GlobalVariable>(val) &&
                SVFUtil::cast<GlobalVariable>(val)->hasInitializer() &&
                SVFUtil::isa<ConstantStruct>(
                    SVFUtil::cast<GlobalVariable>(val)->getInitializer()))
            typeinfo->setFlag(ObjTypeInfo::CONST_STRUCT_OBJ);
        else
            typeinfo->setFlag(ObjTypeInfo::VAR_STRUCT_OBJ);
    }
    else if (elemTy->isPointerTy())
    {
        isPtrObj = true;
    }

    if (isPtrObj)
        typeinfo->setFlag(ObjTypeInfo::HASPTR_OBJ);
}

/*!
 * Analyse types of heap and static objects
 */
void SymbolTableBuilder::analyzeHeapObjType(ObjTypeInfo* typeinfo, const Value* val)
{
    if(const Value* castUse = getUniqueUseViaCastInst(val))
    {
        typeinfo->setFlag(ObjTypeInfo::HEAP_OBJ);
        typeinfo->resetTypeForHeapStaticObj(
            LLVMModuleSet::getLLVMModuleSet()->getSVFType(castUse->getType()));
        const Type* heapLayout = nullptr;
        if (ObjTypeInference* ti =
                LLVMModuleSet::getLLVMModuleSet()->getTypeInference())
            heapLayout = ti->inferObjType(castUse);
        analyzeObjType(typeinfo, castUse, heapLayout);
    }
    else
    {
        typeinfo->setFlag(ObjTypeInfo::HEAP_OBJ);
        typeinfo->setFlag(ObjTypeInfo::HASPTR_OBJ);
    }
}

/*!
 * Analyse types of heap and static objects
 */
void SymbolTableBuilder::analyzeStaticObjType(ObjTypeInfo* typeinfo, const Value* val)
{
    if(const Value* castUse = getUniqueUseViaCastInst(val))
    {
        typeinfo->setFlag(ObjTypeInfo::STATIC_OBJ);
        typeinfo->resetTypeForHeapStaticObj(
            LLVMModuleSet::getLLVMModuleSet()->getSVFType(castUse->getType()));
        const Type* staticLayout = nullptr;
        if (ObjTypeInference* ti =
                LLVMModuleSet::getLLVMModuleSet()->getTypeInference())
            staticLayout = ti->inferObjType(castUse);
        analyzeObjType(typeinfo, castUse, staticLayout);
    }
    else
    {
        typeinfo->setFlag(ObjTypeInfo::HEAP_OBJ);
        typeinfo->setFlag(ObjTypeInfo::HASPTR_OBJ);
    }
}

/*!
 * Initialize the type info of an object
 */
void SymbolTableBuilder::initTypeInfo(ObjTypeInfo* typeinfo, const Value* val,
                                      const Type* objTy)
{

    u32_t objSize = 1;
    // Global variable
    if (SVFUtil::isa<Function>(val))
    {
        typeinfo->setFlag(ObjTypeInfo::FUNCTION_OBJ);
        analyzeObjType(typeinfo, val, objTy);
        objSize = getObjSize(objTy);
    }
    else if(const AllocaInst* allocaInst = SVFUtil::dyn_cast<AllocaInst>(val))
    {
        typeinfo->setFlag(ObjTypeInfo::STACK_OBJ);
        analyzeObjType(typeinfo, val, objTy);
        /// This is for `alloca <ty> <NumElements>`. For example, `alloca i64 3` allocates 3 i64 on the stack (objSize=3)
        /// In most cases, `NumElements` is not specified in the instruction, which means there is only one element (objSize=1).
        if(const ConstantInt* sz = SVFUtil::dyn_cast<ConstantInt>(allocaInst->getArraySize()))
            objSize = sz->getZExtValue() * getObjSize(objTy);
        else
            objSize = getObjSize(objTy);
    }
    else if(SVFUtil::isa<GlobalVariable>(val))
    {
        typeinfo->setFlag(ObjTypeInfo::GLOBVAR_OBJ);
        if(isConstantObjSym(val))
            typeinfo->setFlag(ObjTypeInfo::CONST_GLOBAL_OBJ);
        analyzeObjType(typeinfo, val, objTy);
        objSize = getObjSize(objTy);
    }
    else if (SVFUtil::isa<Instruction>(val) &&
             isHeapAllocExtCall(
                 LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(
                     SVFUtil::cast<Instruction>(val))))
    {
        analyzeHeapObjType(typeinfo,val);
        // Heap object, label its field as infinite here
        objSize = typeinfo->getMaxFieldOffsetLimit();
    }
    else if(ArgInProgEntryFunction(val))
    {
        analyzeStaticObjType(typeinfo,val);
        // user input data, label its field as infinite here
        objSize = typeinfo->getMaxFieldOffsetLimit();
    }
    else if(LLVMUtil::isConstDataOrAggData(val))
    {
        typeinfo->setFlag(ObjTypeInfo::CONST_DATA);
        objSize = getNumOfFlattenElements(val->getType());
    }
    else
    {
        assert("what other object do we have??");
        abort();
    }

    // Reset maxOffsetLimit if it is over the total fieldNum of this object
    if(typeinfo->getMaxFieldOffsetLimit() > objSize)
        typeinfo->setNumOfElements(objSize);
}

/*!
 * Return size of this Object
 */
u32_t SymbolTableBuilder::getObjSize(const Type* ety)
{
    assert(ety && "type is null?");
    u32_t numOfFields = 1;
    if (SVFUtil::isa<StructType, ArrayType>(ety))
    {
        numOfFields = getNumOfFlattenElements(ety);
    }
    return numOfFields;
}

/// Number of flattened elements of an array or struct
u32_t SymbolTableBuilder::getNumOfFlattenElements(const Type* T)
{
    if(Options::ModelArrays())
        return getOrAddSVFTypeInfo(T)->getNumOfFlattenElements();
    else
        return getOrAddSVFTypeInfo(T)->getNumOfFlattenFields();
}

StInfo* SymbolTableBuilder::getOrAddSVFTypeInfo(const Type* T)
{
    return LLVMModuleSet::getLLVMModuleSet()->getSVFType(T)->getTypeInfo();
}
