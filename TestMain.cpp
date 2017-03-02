/* 
 * File:   TestMain
 * Author: mamad
 *
 * Created on Mar 1, 2017, 4:21:42 PM
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <vector>
//should be main
int tstmain(int argc, char** argv) {
    std::vector<const char*> args(argv, argv + argc);
    args.push_back("-v"); // Verbose output (mandatory!)
    args.push_back("-c"); // Colored output (optional)

    return RUN_ALL_TESTS(args.size(), &args[0]);
}
