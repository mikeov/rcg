# RCG
## Create and analyze c/c++ reverse call graph.

Parse gcc RTL files emitted by gcc with -fdump-rtl-expand option, create reverse call graph traversal, then use call graph to find call paths of interest.

To build:
  
    $ c++ -O2 rcg.cc -o rcg

    $ rcg
    Usage: rcg [options] function1 function2 ... < rtl-input
    [-d]          -- debug, prints into standard error all graph edges (unless
            invoked with -egypt) and include / exclude processing
    [-egypt]      -- Graphviz input format created by egypt script. Default is rtl
            format created by gcc -fdump-rtl-expand
    [-rtll]       -- standard in is list of rtl file names, one file name per line,
            instead of rtl input
    [-no-refs]    -- produce direct call graph, by not including functions
            references when parsing rtl (passing / assigning function addresses)
    The prior options control reverse call graph construction.
    These options must placed before the following options that control graph
            traversal.
    [-i function] -- include call paths with functions names
    [-e function] -- exclude call paths with functions names
    [-ic]         -- clear include functions list
    [-ec]         -- clear exclude functions list
    [-il]         -- file with list of include functions, one function name per line
    [-el]         -- file with list of exclude functions, one function name per line
    [-si]         -- stop traversal if matches function name in include list
            (default); has effect only if include list is no empty; call path with
            excluded functions that occur in the path before include functions will
            not be excluded / filtered out
    [-ci]         -- continue traversal if matches include function
    With -egypt the input is the output of "egypt" perl script which converts files
            created by gcc -fdump-rtl-expand into Graphviz input format.
    The output is call paths for the specified functions / methods.
    A practical invocation example:
    find path_to_build_directory -type f -name '*.expand' | rcg -rtll function1 function2
