//===- wpa.cpp -- Whole program analysis -------------------------------------//
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
//===-----------------------------------------------------------------------===//

/*
 // Whole Program Pointer Analysis
 //
 // Author: Yulei Sui,
 */

#include "SVF-LLVM/LLVMUtil.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVF-LLVM/SVFIRGetter.h"
#include "WPA/WPAPass.h"
#include "Util/CommandLine.h"
#include "Util/Options.h"
#include "SVFIR/SVFFileSystem.h"
#include "Diff/SourceDiff.h"
#include "Diff/IRDiff.h"
#include <cstdlib>
#include <cstdio>

using namespace llvm;
using namespace std;
using namespace SVF;

void diff()
{
    // double starttime = stat->getClk();   
    SourceDiffHandler *sourceDiff = SourceDiffHandler::getSourceDiffHandler();

    //std::cout << "sourceDiff.display:" << std::endl;
    sourceDiff->handle();
    //sourceDiff.display();
    //sourceDiff.dump();
    // double endtime = stat->getClk();
    // stat->StatTimeOfSourceDiff(starttime, endtime);

    // starttime = stat->getClk();
    IRDiffHandler* irDiff = IRDiffHandler::getIRDiffHandler();
    irDiff->parse();
    
    auto add = irDiff->getInstAddSet();
    auto del = irDiff->getInstDeleteSet();
    if (add.empty() && del.empty())
    {
        SVFUtil::outs() << "No inst changed.\n";
        return;
    }
    SVFUtil::outs() << "Add insts: " << add.size() << "\n";
    SVFUtil::outs() << "Del insts: " << del.size() << "\n";

    // endtime = stat->getClk();
    // stat->StatTimeOfIrDiff(starttime, endtime);

    // irDiff->dump("irdiffresult.txt",true);
}

int main(int argc, char** argv)
{
    auto moduleNameVec =
        OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                 "[options] <input-bitcode...>");

    // Refers to content of a singleton unique_ptr<SVFIR> in SVFIR.
    SVFIR* pag;

    if (Options::ReadJson())
    {
        pag = SVFIRReader::read(moduleNameVec.front());
    }
    else
    {
        if (Options::WriteAnder() == "ir_annotator")
        {
            LLVMModuleSet::preProcessBCs(moduleNameVec);
        }

        SVFModule* svfModule = LLVMModuleSet::buildSVFModule(moduleNameVec);
        if (svfModule == nullptr)
        {
            SVFUtil::errs() << "Failed to load input bitcode module(s).\n";
            return 1;
        }

        /// Build SVFIR
        SVFIRBuilder builder(svfModule);
        pag = builder.build();
        if (pag == nullptr)
        {
            SVFUtil::errs() << "Failed to build SVFIR from input module(s).\n";
            return 1;
        }
    }
    if (Options::irdiff()) {
        diff();
        SVFIRGetter* irGetter = SVFIRGetter::getSVFIRGetter();
    }
    WPAPass wpa;
    wpa.runOnModule(pag);

    // Temporary workaround for opaque-pointer migration: avoid teardown crash
    // in static SVFIR/ICFG destruction after successful analysis.
    std::fflush(nullptr);
    std::_Exit(0);
}
