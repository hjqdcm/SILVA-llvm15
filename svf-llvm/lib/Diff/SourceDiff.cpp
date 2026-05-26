// #include <filesystem>
#include "Diff/SourceDiff.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include <unistd.h>

using namespace SVF;
using namespace SVFUtil;

SourceDiffHandler* SourceDiffHandler:: sourceDiffHandler = nullptr;
std::string SourceDiffHandler::beforeDir;
std::string SourceDiffHandler::afterDir;
std::string SourceDiffHandler::beforeRootDir;
std::string SourceDiffHandler::afterRootDir;

void SourceDiffHandler::handle()
{
    // Unique name avoids parallel wpa runs in the same cwd clobbering each other.
    std::string realSrcDiff =
        "real_" /*+ std::to_string(static_cast<long long>(getpid())) + "_"*/ + sourceDiff;
    // if (std::filesystem::exists(realSrcDiff)) {
    //     std::cout << "realSrcDiff文件已经存在" << std::endl;
    //     return;
    // }
    ifstream in(sourceDiff, ios::in);
    ofstream out(realSrcDiff, ios::out);
    string line;
    bool flag = true;

    if (!in)
    {
        cout << "Can't read source code diff file." << endl;
    }
    else
    {
        while (getline(in, line))
        {
            if (line.empty())
                continue;
            char ch = line.front();
            if ('B' == ch) {
                continue;
            }
            else if ('<' == ch || '>' == ch || '-' == ch)
            {
                if(flag)
                    out << line << "\n";
                continue;
            }
            else if ('d' == ch)
            {
                std::vector<string> diffCmd;
                splitString(line, diffCmd, " ");
                if (diffCmd.size() < 2)
                    continue;
                before = diffCmd[diffCmd.size() - 2];
                after = diffCmd[diffCmd.size() - 1];
                flag = isSourceFile(before);
                if(flag)
                    out << line << "\n";
                continue;
            }
            if(flag){
                out << line << "\n";
                parse(sourceDiff, line);
            }
        }
    }
}

void SourceDiffHandler::parse(string sourceDiff, string line)
{
    int n;
    string path;
    if (-1 != (n = line.find('a')))
    {
        string str = line.substr(n + 1);
        vector<string> rows;
        splitString(str, rows, ",");
        if (rows.empty())
            return;
        int row1;
        int row2;
        istringstream i1(rows[0]);
        i1 >> row1;
        row2 = row1;
        if (2 == rows.size())
        {
            istringstream i2(rows[1]);
            i2 >> row2;
        }
        if(SVF::Options::relapath())
            path = getRelaPath(afterRootDir, after);
        else
            path = after;
        sourceDiffInfo info(1, path, row1, row2);
        addDiff[path].push_back(info);
    }
    else if (-1 != (n = line.find('d')))
    {
        string str = line.substr(0, n);
        vector<string> rows;
        splitString(str, rows, ",");
        if (rows.empty())
            return;
        int row1;
        int row2;
        istringstream i1(rows[0]);
        i1 >> row1;
        row2 = row1;
        if (2 == rows.size())
        {
            istringstream i2(rows[1]);
            i2 >> row2;
        }
        if(SVF::Options::relapath())
            path = getRelaPath(beforeRootDir, before);
        else
            path = before;
        sourceDiffInfo info(2, path, row1, row2);
        deleteDiff[path].push_back(info);
    }
    else if (-1 != (n = line.find('c')))
    {
        string str1 = line.substr(n + 1);
        vector<string> rows1;
        splitString(str1, rows1, ",");
        if (rows1.empty())
            return;
        int row11;
        int row12;
        istringstream i11(rows1[0]);
        i11 >> row11;
        row12 = row11;
        if (2 == rows1.size())
        {
            istringstream i12(rows1[1]);
            i12 >> row12;
        }

        if(SVF::Options::relapath())
            path = getRelaPath(afterRootDir, after);
        else
            path = after;
        sourceDiffInfo info1(1, path, row11, row12);
        addDiff[path].push_back(info1);
        
        string str2 = line.substr(0, n);
        vector<string> rows2;
        splitString(str2, rows2, ",");
        if (rows2.empty())
            return;
        int row21;
        int row22;
        istringstream i21(rows2[0]);
        i21 >> row21;
        row22 = row21;
        if (2 == rows2.size())
        {
            istringstream i22(rows2[1]);
            i22 >> row22;
        }

        if(SVF::Options::relapath())
            path = getRelaPath(beforeRootDir, before);
        else
            path = before;
        sourceDiffInfo info2(2, path, row21, row22);
        deleteDiff[path].push_back(info2);
    }
}

// void SourceDiffHandler::display()
// {
//     cout << "add" << endl;
//     for (auto e : addVec)
//     {
//         cout << e.getType() << " " << e.getFile() << " " << e.getRow() << endl;
//     }
//     cout << "delete" << endl;
//     for (auto e : deleteVec)
//     {
//         cout << e.getType() << " " << e.getFile() << " " << e.getRow() << endl;
//     }
// }

// void SourceDiffHandler::dump(string s)
// {
//     ofstream out(s, ios::out);
//     out << "add\n";
//     for (auto e : addVec)
//     {
//         out << e.getType() << " " << e.getFile() << " " << e.getRow() << "\n";
//     }
//     out << "delete\n";
//     for (auto e : deleteVec)
//     {
//         out << e.getType() << " " << e.getFile() << " " << e.getRow() << "\n";
//     }
// }