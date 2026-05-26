//===- AndersenStat.cpp -- Statistics of Andersen's analysis------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2017>  <Yulei Sui>
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
 * AndersenStat.cpp
 *
 *  Created on: Oct 12, 2013
 *      Author: Yulei Sui
 */

#include "MemoryModel/PointerAnalysis.h"
#include "WPA/WPAStat.h"
#include "WPA/Andersen.h"
#include "WPA/AndersenInc.h"

using namespace SVF;
using namespace SVFUtil;
using namespace std;

u32_t AndersenIncStat::_MaxPtsSize = 0;
u32_t AndersenIncStat::_NumOfCycles = 0;
u32_t AndersenIncStat::_NumOfPWCCycles = 0;
u32_t AndersenIncStat::_NumOfNodesInCycles = 0;
u32_t AndersenIncStat::_MaxNumOfNodesInSCC = 0;

const char* AndersenIncStat::CollapseTime = "CollapseTime";
/*!
 * Constructor
 */
AndersenIncStat::AndersenIncStat(AndersenInc* p): PTAStat(p),pta(p)
{
    _NumOfNullPtr = 0;
    _NumOfConstantPtr= 0;
    _NumOfBlackholePtr = 0;
    startClk();
}

/*!
 * Collect cycle information
 */
void AndersenIncStat::collectCycleInfo(SConstraintGraph* consCG)
{
    _NumOfCycles = 0;
    _NumOfPWCCycles = 0;
    _NumOfNodesInCycles = 0;
    NodeSet repNodes;
    repNodes.clear();
    for(SConstraintGraph::iterator it = consCG->begin(), eit = consCG->end(); it!=eit; ++it)
    {
        // sub nodes have been removed from the constraint graph, only rep nodes are left.
        NodeID repNode = consCG->sccRepNode(it->first);
        NodeBS& subNodes = consCG->sccSubNodes(repNode);
        NodeBS clone = subNodes;
        for (NodeBS::iterator it = subNodes.begin(), eit = subNodes.end(); it != eit; ++it)
        {
            NodeID nodeId = *it;
            PAGNode* pagNode = pta->getPAG()->getGNode(nodeId);
            if (SVFUtil::isa<ObjVar>(pagNode) && pta->isFieldInsensitive(nodeId))
            {
                NodeID baseId = consCG->getBaseObjVar(nodeId);
                clone.reset(nodeId);
                clone.set(baseId);
            }
        }
        u32_t num = clone.count();
        if (num > 1)
        {
            if(repNodes.insert(repNode).second)
            {
                _NumOfNodesInCycles += num;
                if(consCG->isPWCNode(repNode))
                    _NumOfPWCCycles ++;
            }
            if( num > _MaxNumOfNodesInSCC)
                _MaxNumOfNodesInSCC = num;
        }
    }
    _NumOfCycles += repNodes.size();
}

void AndersenIncStat::constraintGraphStat()
{


    SConstraintGraph* consCG = pta->getSConstraintGraph();

    u32_t numOfCopys = 0;
    u32_t numOfGeps = 0;
    // collect copy and gep edges
    for(SConstraintEdge::SConstraintEdgeSetTy::iterator it = consCG->getDirectSCGEdges().begin(),
            eit = consCG->getDirectSCGEdges().end(); it!=eit; ++it)
    {
        if(SVFUtil::isa<CopySCGEdge>(*it))
            numOfCopys++;
        else if(SVFUtil::isa<GepSCGEdge>(*it))
            numOfGeps++;
        else
            assert(false && "what else!!");
    }

    u32_t totalNodeNumber = 0;
    u32_t cgNodeNumber = 0;
    u32_t objNodeNumber = 0;
    u32_t addrtotalIn = 0;
    u32_t addrmaxIn = 0;
    u32_t addrmaxOut = 0;
    u32_t copytotalIn = 0;
    u32_t copymaxIn = 0;
    u32_t copymaxOut = 0;
    u32_t loadtotalIn = 0;
    u32_t loadmaxIn = 0;
    u32_t loadmaxOut = 0;
    u32_t storetotalIn = 0;
    u32_t storemaxIn = 0;
    u32_t storemaxOut = 0;


    for (SConstraintGraph::SConstraintNodeIDToNodeMapTy::iterator nodeIt = consCG->begin(), nodeEit = consCG->end();
            nodeIt != nodeEit; nodeIt++)
    {
        totalNodeNumber++;
        if(nodeIt->second->getInEdges().empty() && nodeIt->second->getOutEdges().empty())
            continue;
        cgNodeNumber++;
        if(SVFUtil::isa<ObjVar>(pta->getPAG()->getGNode(nodeIt->first)))
            objNodeNumber++;

        u32_t nCopyIn = nodeIt->second->getDirectInEdges().size();
        if(nCopyIn > copymaxIn)
            copymaxIn = nCopyIn;
        copytotalIn +=nCopyIn;
        u32_t nCopyOut = nodeIt->second->getDirectOutEdges().size();
        if(nCopyOut > copymaxOut)
            copymaxOut = nCopyOut;
        u32_t nLoadIn = nodeIt->second->getLoadInEdges().size();
        if(nLoadIn > loadmaxIn)
            loadmaxIn = nLoadIn;
        loadtotalIn +=nLoadIn;
        u32_t nLoadOut = nodeIt->second->getLoadOutEdges().size();
        if(nLoadOut > loadmaxOut)
            loadmaxOut = nLoadOut;
        u32_t nStoreIn = nodeIt->second->getStoreInEdges().size();
        if(nStoreIn > storemaxIn)
            storemaxIn = nStoreIn;
        storetotalIn +=nStoreIn;
        u32_t nStoreOut = nodeIt->second->getStoreOutEdges().size();
        if(nStoreOut > storemaxOut)
            storemaxOut = nStoreOut;
        u32_t nAddrIn = nodeIt->second->getAddrInEdges().size();
        if(nAddrIn > addrmaxIn)
            addrmaxIn = nAddrIn;
        addrtotalIn +=nAddrIn;
        u32_t nAddrOut = nodeIt->second->getAddrOutEdges().size();
        if(nAddrOut > addrmaxOut)
            addrmaxOut = nAddrOut;
    }
    double storeavgIn = (double)storetotalIn/cgNodeNumber;
    double loadavgIn = (double)loadtotalIn/cgNodeNumber;
    double copyavgIn = (double)copytotalIn/cgNodeNumber;
    double addravgIn = (double)addrtotalIn/cgNodeNumber;
    double avgIn = (double)(addrtotalIn + copytotalIn + loadtotalIn + storetotalIn)/cgNodeNumber;


    PTNumStatMap["NumOfCGNode"] = totalNodeNumber;
    PTNumStatMap["TotalValidNode"] = cgNodeNumber;
    PTNumStatMap["TotalValidObjNode"] = objNodeNumber;
    PTNumStatMap["NumOfCGEdge"] = consCG->getLoadSCGEdges().size() + consCG->getStoreSCGEdges().size()
                                  + numOfCopys + numOfGeps;
    PTNumStatMap["NumOfAddrs"] =  consCG->getAddrSCGEdges().size();
    PTNumStatMap["NumOfCopys"] = numOfCopys;
    PTNumStatMap["NumOfGeps"] =  numOfGeps;
    PTNumStatMap["NumOfLoads"] = consCG->getLoadSCGEdges().size();
    PTNumStatMap["NumOfStores"] = consCG->getStoreSCGEdges().size();
    PTNumStatMap["MaxInCopyEdge"] = copymaxIn;
    PTNumStatMap["MaxOutCopyEdge"] = copymaxOut;
    PTNumStatMap["MaxInLoadEdge"] = loadmaxIn;
    PTNumStatMap["MaxOutLoadEdge"] = loadmaxOut;
    PTNumStatMap["MaxInStoreEdge"] = storemaxIn;
    PTNumStatMap["MaxOutStoreEdge"] = storemaxOut;
    PTNumStatMap["AvgIn/OutStoreEdge"] = storeavgIn;
    PTNumStatMap["MaxInAddrEdge"] = addrmaxIn;
    PTNumStatMap["MaxOutAddrEdge"] = addrmaxOut;
    timeStatMap["AvgIn/OutCopyEdge"] = copyavgIn;
    timeStatMap["AvgIn/OutLoadEdge"] = loadavgIn;
    timeStatMap["AvgIn/OutAddrEdge"] = addravgIn;
    timeStatMap["AvgIn/OutEdge"] = avgIn;

    PTAStat::printStat("Constraint Graph Stats");
}
/*!
 * Stat null pointers
 */
void AndersenIncStat::statNullPtr()
{

    _NumOfNullPtr = 0;
    for (SVFIR::iterator iter = pta->getPAG()->begin(), eiter = pta->getPAG()->end();
            iter != eiter; ++iter)
    {
        NodeID pagNodeId = iter->first;
        PAGNode* pagNode = iter->second;
        if (SVFUtil::isa<ValVar>(pagNode) == false)
            continue;
        SVFStmt::SVFStmtSetTy& inComingStore = pagNode->getIncomingEdges(SVFStmt::Store);
        SVFStmt::SVFStmtSetTy& outGoingLoad = pagNode->getOutgoingEdges(SVFStmt::Load);
        if (inComingStore.empty()==false || outGoingLoad.empty()==false)
        {
            ///TODO: change the condition here to fetch the points-to set
            const PointsTo& pts = pta->getPts(pagNodeId);
            if (pta->containBlackHoleNode(pts))
                _NumOfBlackholePtr++;

            if (pta->containConstantNode(pts))
                _NumOfConstantPtr++;

            if(pts.empty())
            {
                std::string str;
                std::stringstream rawstr(str);
                if (!SVFUtil::isa<DummyValVar>(pagNode) && !SVFUtil::isa<DummyObjVar>(pagNode) )
                {
                    // if a pointer is in dead function, we do not care
                    if(pagNode->getValue()->ptrInUncalledFunction() == false)
                    {
                        _NumOfNullPtr++;
                        rawstr << "##Null Pointer : (NodeID " << pagNode->getId()
                               << ") PtrName:" << pagNode->getValue()->getName()
                               << " Src:" << pagNode->getValue()->getSourceLoc();
                        writeWrnMsg(rawstr.str());
                        //pagNode->getValue()->dump();
                    }
                }
                else
                {
                    _NumOfNullPtr++;
                    rawstr << "##Null Pointer : (NodeID " << pagNode->getId()
                           << ") Src:" << pagNode->getValue()->getSourceLoc();
                    writeWrnMsg(rawstr.str());
                }
            }
        }
    }

}

/*!
 * Start here
 */
void AndersenIncStat::performStat()
{

    assert(SVFUtil::isa<AndersenInc>(pta) && "not an andersen pta pass!! what else??");
    endClk();

    SVFIR* pag = pta->getPAG();
    SConstraintGraph* consCG = pta->getSConstraintGraph();

    // collect constraint graph cycles
    collectCycleInfo(consCG);

    // stat null ptr number
    statNullPtr();

    u32_t totalPointers = 0;
    u32_t totalTopLevPointers = 0;
    u32_t totalPtsSize = 0;
    u32_t totalTopLevPtsSize = 0;
    for (SVFIR::iterator iter = pta->getPAG()->begin(), eiter = pta->getPAG()->end();
            iter != eiter; ++iter)
    {
        NodeID node = iter->first;
        const PointsTo& pts = pta->getPts(node);
        u32_t size = pts.count();
        totalPointers++;
        totalPtsSize+=size;

        if(pta->getPAG()->isValidTopLevelPtr(pta->getPAG()->getGNode(node)))
        {
            totalTopLevPointers++;
            totalTopLevPtsSize+=size;
        }

        if(size > _MaxPtsSize )
            _MaxPtsSize = size;
    }


    PTAStat::performStat();

    constraintGraphStat();

    timeStatMap["TotalTime"] = (endTime - startTime)/TIMEINTERVAL;

    timeStatMap["ExhaustivePTATime"] = AndersenInc::timeOfExhaustivePTA;
    timeStatMap["IncrementalPTATime"] = AndersenInc::timeOfIncrementalPTA;
    timeStatMap["DeletionPTATime"] = AndersenInc::timeOfDeletionPTA;
    timeStatMap["InsertionPTATime"] = AndersenInc::timeOfInsertionPTA;
    timeStatMap["SCCDeletionTime"] = AndersenInc::timeOfDeletionSCC;
    timeStatMap["SCCRedetectNum"] = AndersenInc::numOfRedetectSCC;
    timeStatMap["SCGDeleteTime"] = AndersenInc::timeOfSCGDelete;
    timeStatMap["SCGRebuildTime"] = AndersenInc::timeOfSCGRebuild;
    timeStatMap["TempGBuildTime"] = SConstraintGraph::timeOfBuildTempG;
    timeStatMap["SaveSCCNum"] = SConstraintGraph::numOfSaveTempG;
    timeStatMap["SCCFindTime"] = SConstraintGraph::timeOfSCCFind;
    timeStatMap["ResetRepSubTime"] = SConstraintGraph::timeOfResetRepSub;
    timeStatMap["SCCEdgeRestoreTime"] = SConstraintGraph::timeOfSCCEdgeRestore;
    timeStatMap["SCCEdgeRestoreNum"] = SConstraintGraph::numOfSCCRestore;
    timeStatMap["EdgeCollectionTime"] = SConstraintGraph::timeOfCollectEdge;
    timeStatMap["EdgeRemovalTime"] = SConstraintGraph::timeOfRemoveEdge;
    timeStatMap["EdgeAdditionTime"] = SConstraintGraph::timeOfAddEdge;
    timeStatMap["SCCInsertionTime"] = AndersenInc::timeOfInsertionSCC;
    timeStatMap["PropDeletionTime"] = AndersenInc::timeOfDeletionProp;
    timeStatMap["PropInsertionTime"] = AndersenInc::timeOfInsertionProp;

    timeStatMap["SCCDetectTime"] = AndersenInc::timeOfSCCDetection;
    timeStatMap["SCCDetectTimeIPAIns"] = AndersenInc::timeOfSCCDetectionIPAIns;
    timeStatMap["SCCDetectTimeIPADel"] = AndersenInc::timeOfSCCDetectionIPADel;
    timeStatMap["SCCDetectTimeIns"] = AndersenInc::timeOfSCCDetectionIns;
    timeStatMap["SCCDetectTimeDel"] = AndersenInc::timeOfSCCDetectionDel;
    
    timeStatMap["SCCMergeTime"] =  AndersenInc::timeOfSCCMerges;
    timeStatMap[CollapseTime] =  AndersenInc::timeOfCollapse;
    timeStatMap["CollapsePWCTime"] = AndersenInc::timeOfCollapsePWC;
    
    timeStatMap["LoadStoreTime"] =  AndersenInc::timeOfProcessLoadStore;
    timeStatMap["CopyGepTime"] =  AndersenInc::timeOfProcessCopyGep;
    timeStatMap["UpdateCGTime"] =  AndersenInc::timeOfUpdateCallGraph;

    PTNumStatMap["TotalPointers"] = pag->getValueNodeNum() + pag->getFieldValNodeNum();
    PTNumStatMap["TotalObjects"] = pag->getObjectNodeNum() + pag->getFieldObjNodeNum();


    PTNumStatMap["AddrProcessed"] = AndersenInc::numOfProcessedAddr;
    PTNumStatMap["CopyProcessed"] = AndersenInc::numOfProcessedCopy;
    PTNumStatMap["GepProcessed"] = AndersenInc::numOfProcessedGep;
    PTNumStatMap["LoadProcessed"] = AndersenInc::numOfProcessedLoad;
    PTNumStatMap["StoreProcessed"] = AndersenInc::numOfProcessedStore;

    PTNumStatMap["NumOfSFRs"] = AndersenInc::numOfSfrs;
    PTNumStatMap["NumOfFieldExpand"] = AndersenInc::numOfFieldExpand;

    PTNumStatMap["Pointers"] = pag->getValueNodeNum();
    PTNumStatMap["MemObjects"] = pag->getObjectNodeNum();
    PTNumStatMap["DummyFieldPtrs"] = pag->getFieldValNodeNum();
    PTNumStatMap["FieldObjs"] = pag->getFieldObjNodeNum();

    timeStatMap["AvgPtsSetSize"] = (double)totalPtsSize/totalPointers;;
    timeStatMap["AvgTopLvlPtsSize"] = (double)totalTopLevPtsSize/totalTopLevPointers;;

    PTNumStatMap["MaxPtsSetSize"] = _MaxPtsSize;

    PTNumStatMap["SolveIterations"] = pta->numOfIteration;

    PTNumStatMap["IndCallSites"] = consCG->getIndirectCallsites().size();
    PTNumStatMap["IndEdgeSolved"] = pta->getNumOfResolvedIndCallEdge();

    PTNumStatMap["NumOfSCCDetect"] = AndersenInc::numOfSCCDetection;
    PTNumStatMap["NumOfSCCDetectIPAIns"] = AndersenInc::numOfSCCDetectionIPAIns;
    PTNumStatMap["NumOfSCCDetectIPADel"] = AndersenInc::numOfSCCDetectionIPADel;
    PTNumStatMap["NumOfSCCDetectIns"] = AndersenInc::numOfSCCDetectionIns;
    PTNumStatMap["NumOfSCCDetectDel"] = AndersenInc::numOfSCCDetectionDel;
    
    
    PTNumStatMap["TotalCycleNum"] = _NumOfCycles;
    PTNumStatMap["TotalPWCCycleNum"] = _NumOfPWCCycles;
    PTNumStatMap["NodesInCycles"] = _NumOfNodesInCycles;
    PTNumStatMap["MaxNodesInSCC"] = _MaxNumOfNodesInSCC;
    PTNumStatMap["NullPointer"] = _NumOfNullPtr;
    PTNumStatMap["PointsToConstPtr"] = _NumOfConstantPtr;
    PTNumStatMap["PointsToBlkPtr"] = _NumOfBlackholePtr;

    PTAStat::printStat("Andersen Pointer Analysis Stats");
}
