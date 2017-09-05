//---------------------------------------------------------- -*- Mode: C++ -*-
// $Id$
//
// Created 2017/09/02
// Author: Mike Ovsiannikov
//
//
// Licensed under the Apache License, Version 2.0
// (the "License"); you may not use this file except in compliance with
// the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
// implied. See the License for the specific language governing
// permissions and limitations under the License.
//
// Code to parse gcc rtl files, create reverse call graph traversal, then use
// call graph to find call path of interest.
//
// The following can be used to build the executable:
// c++ -O2 rcg.cc -o rcg
// Program command line arguments description can be found in "usage" message in
// main().
//
//----------------------------------------------------------------------------

#include <map>
#include <set>
#include <algorithm>
#include <vector>
#include <string>
#include <ostream>
#include <istream>
#include <iostream>
#include <fstream>

#include <string.h>
#include <unistd.h>
#include <stdio.h>
#include <errno.h>
#include <fcntl.h>

namespace
{
using std::cerr;
using std::istream;
using std::ostream;
using std::string;
using std::find;
using std::ifstream;

template<typename DDT, typename NT>
    static const NT&
demangle(
    const DDT& dict,
    const NT&  name)
{
    typename DDT::const_iterator const it = dict.find(name);
    return (dict.end() == it ? name : it->second);
}

template<typename FT, typename DDT, typename T>
    static void
for_each_edge_demangle_self(
    FT&        func,
    const DDT& demangle_dict,
    const T&   dict,
    const T*   calls_dict,
    bool       unique_flag)
{
    for (typename T::const_iterator
            it = dict.begin(); dict.end() != it; ++it) {
        typename T::mapped_type const& calls = it->second;
        for (typename T::mapped_type::const_iterator
                cit = calls.begin(); calls.end() != cit; ++cit) {
            typename T::const_iterator oit;
            if (calls_dict &&
                    ((dict.end() == dict.find(*cit) &&
                    calls_dict->end() == calls_dict->find(*cit)) ||
                    (unique_flag &&
                    calls_dict->end() != (oit = calls_dict->find(it->first)) &&
                    oit->second.end() != oit->second.find(*cit)))) {
                continue;
            }
            func(demangle(demangle_dict, it->first),
                demangle(demangle_dict, *cit));
        }
    }
}

template<typename FT, typename DDT, typename T>
    static void
for_each_edge_demangle(
    FT&        func,
    const DDT& demangle,
    const T&   calls,
    const T&   refs,
    bool       unique_flag = true)
{
    const T* k_no_ref_filter = 0;
    for_each_edge_demangle_self(
        func, demangle, calls, k_no_ref_filter, unique_flag);
    for_each_edge_demangle_self(func, demangle, refs, &calls, unique_flag);
}

const int k_space_symbol = ' ';

    static inline const char*
skip_white_space(
    const char* ptr,
    const char* end)
{
    while (ptr < end && (*ptr & 0xFF) <= k_space_symbol) {
        ptr++;
    }
    return ptr;
}

    static inline const char*
skip_non_white_space(
    const char* ptr,
    const char* end)
{
    while (ptr < end && k_space_symbol < (*ptr & 0xFF)) {
        ptr++;
    }
    return ptr;
}

    static inline const char*
sym_search(
    int         sym,
    const char* ptr,
    const char* end)
{
    return reinterpret_cast<const char*>(memchr(ptr, sym, end - ptr));
}

    static inline const char*
token_search(
    const char* token,
    size_t      token_len,
    const char* ptr,
    const char* end)
{
    if (token_len <= 1) {
        return (token_len <= 0 ? ptr : sym_search(*token, ptr, end));
    }
    const int    sym  = *token;
    const char*  cur  = ptr;
    const char*  tok  = token + 1;
    const size_t len  = token_len - 1;
    const char*  last = end - len;
    while (cur < last &&
            (cur = sym_search(sym, cur, last)) &&
            0 != memcmp(cur + 1, tok, len)) {
        cur++;
    }
    return ((cur && cur < last) ? cur : 0);
}

    static inline string
get_call_name(
    const char* prefix,
    size_t      prefix_len,
    const char* ptr,
    const char* end)
{
    const char* pref = token_search(prefix, prefix_len, ptr, end);
    if (pref) {
        pref += prefix_len;
        const char* pref_end;
        if ((pref = sym_search('"', pref, end)) &&
                ++pref < end &&
                (pref_end = sym_search('"', pref, end))) {
            // Remove ARM short calls caret prefix, if any.
            while ('^' == *pref) {
                ++pref;
            }
            // Remove star that gcc puts in front of "aliased" calls.
            while ('*' == *pref) {
                ++pref;
            }
            return string(pref, pref_end - pref);
        }
    }
    return string();
}

class temp_read_buffer
{
public:
    temp_read_buffer(
        size_t size)
        : m_buf(new char[size])
        {}
    ~temp_read_buffer()
        { delete [] m_buf; }
    char* get()
        { return m_buf; }
private:
    char* const m_buf;
private:
    temp_read_buffer(
        const temp_read_buffer&);
    temp_read_buffer& operator=(
        const temp_read_buffer&);
};

using std::streamsize;

// standard c++ regex appears to be inefficient at the moment --
// 4x "slower" than perl (straight backtracking vs NFA + backtracking?).
// Use "hand crafted" scanner for now.
template<typename IS, typename ES, typename DDT, typename DT, typename DOS>
    static int
rtl_parse(
    IS&  is,
    ES&  oerr,
    DDT& demangle,
    DT&  calls,
    DT&  refs,
    bool include_refs_flag,
    DOS* debug_os = 0)
{
    const char* const func_prefix(";; Function ");
    const size_t      func_prefix_len(strlen(func_prefix));
    const char* const call_prefix("(call");
    const size_t      call_prefix_len(strlen(call_prefix));
    const char* const ref_prefix("(symbol_ref");
    const size_t      ref_prefix_len(strlen(call_prefix));
    const char* const func_name_end(" (");
    const size_t      func_name_end_len(strlen(func_name_end));
    string            func_name;
    const size_t      max_line_len = 1 << 20;
    temp_read_buffer  read_buf(max_line_len + 1);
    char* const       line(read_buf.get());
    int               ret = 0;

    line[max_line_len] = 0;
    const char* line_end = line;
    const char* end      = line_end;
    for (; ;) {
        const char* ptr = skip_white_space(end, line_end);
        end = sym_search('\n', ptr, line_end);
        if (! end) {
            if (line < ptr) {
                memmove(line, ptr, line_end - ptr);
            }
            end = line;
            ptr = line + (line_end - ptr);
            if (line + max_line_len <= ptr) {
                oerr << "line length exsceeds max: " << max_line_len << "\n";
                ret = 1;
                break;
            }
            if (! is.read(const_cast<char*>(ptr), line + max_line_len - ptr) &&
                    is.bad()) {
                oerr << strerror(errno) << "\n";
                ret = 1;
                break;
            }
            const streamsize nrd = is.gcount();
            if (0 < nrd) {
                line_end = ptr + nrd;
                continue;
            }
            if (nrd <= 0) {
                if (ptr <= line) {
                    break;
                }
            }
            end = ptr;
            ptr = line;
        }
        ptr = skip_white_space(ptr, end);
        if (ptr + func_prefix_len < end &&
                0 == memcmp(ptr, func_prefix, func_prefix_len)) {
            ptr += func_prefix_len;
            ptr = skip_white_space(ptr, end);
            const char* const name_beg = ptr;
            ptr = skip_non_white_space(ptr, end);
            const char* const name_end = ptr;
            if (name_beg < ptr) {
                ptr = token_search(func_name_end, func_name_end_len, ptr, end);
                const char* sign_end = ptr;
                if (name_end <= sign_end) {
                    while (name_beg < sign_end &&
                            (sign_end[-1] & 0xFF) <= k_space_symbol) {
                        sign_end--;
                    }
                    ptr = skip_white_space(ptr + func_name_end_len, end);
                    const char* sym_beg = ptr;
                    ptr = skip_non_white_space(ptr, end);
                    if (ptr < end && sym_beg < --ptr && ',' == *ptr) {
                        func_name = string(sym_beg, ptr - sym_beg);
                        calls[func_name];
                        if (ptr - sym_beg != sign_end - name_beg ||
                            0 != memcmp(
                                sym_beg, name_beg, sign_end - name_beg)) {
                            demangle[func_name] =
                                string(name_beg, sign_end - name_beg);
                        }
                    } else {
                        ptr = name_beg;
                    }
                } else {
                    func_name = string(name_beg, name_end - name_beg);
                    calls[func_name];
                    ptr = name_end;
                }
            }
        }
        string call = get_call_name(call_prefix, call_prefix_len, ptr, end);
        if (! call.empty()) {
            calls[func_name].insert(call);
        } else if (include_refs_flag && ! (call = get_call_name(
                ref_prefix, ref_prefix_len, ptr, end)).empty()) {
            refs[func_name].insert(call);
        }
    }
    return ret;
}

typedef std::vector<const void*>            func_callers;
typedef std::map<string, func_callers>      reverse_call_graph;
typedef reverse_call_graph::value_type      call_graph_node;
typedef std::vector<const call_graph_node*> call_path;
typedef std::set<const call_graph_node*>    path_filter;

static ostream* debug_os = 0;

    inline static const call_graph_node*
get_call_graph_node(
    const void* ptr)
{
    return reinterpret_cast<const call_graph_node*>(ptr);
}

    static void
load(
    reverse_call_graph& graph,
    istream&            is)
{
    string const delim("\" [");
    string const sep("\" -> \"");
    const size_t sep_sz = sep.size();
    size_t       calls  = 0;
    string       line;
    while (getline(is, line)) {
        if (line.empty() || '"' != *line.begin() ||
                ';' != *line.rbegin()) {
            continue;
        }
        size_t pos = line.find(sep);
        if (string::npos == pos || pos <= 1) {
            continue;
        }
        const string caller = line.substr(1, pos - 1);
        pos += sep_sz;
        if (line.size() <= pos) {
            continue;
        }
        const size_t end_pos = line.rfind(delim);
        if (string::npos == end_pos || end_pos <= pos) {
            continue;
        }
        const string func = line.substr(pos, end_pos - pos);
        if (debug_os) {
            *debug_os << caller << " " << func << "\n";
        }
        if (func != caller) {
            graph.insert(call_graph_node(func, func_callers())
                ).first->second.push_back(&*graph.insert(
                    call_graph_node(caller, func_callers())).first);
            calls++;
        }
    }
    cerr << "functions: " << graph.size() << " calls: " << calls << "\n";
}

    static void
find_roots(
    const reverse_call_graph& graph,
    const path_filter&        path_include,
    const path_filter&        path_exclude,
    call_path&                path,
    ostream&                  os,
    bool                      in_found_flag,
    bool                      stop_at_include_flag)
{
    const call_graph_node* const func = path.back();
    if (path_exclude.end() != path_exclude.find(func)) {
        if (debug_os) {
            *debug_os << "exclude: " << func->first << "\n";
        }
        return;
    }
    const bool found_flag = in_found_flag ||
        path_include.end() != path_include.find(func);
    if (debug_os && found_flag != in_found_flag) {
        *debug_os << "include: " << func->first << "\n";
    }
    size_t traversed_callers = 0;
    if (! stop_at_include_flag || ! found_flag) {
        const func_callers& callers = func->second;
        for (func_callers::const_iterator
                it = callers.begin(); callers.end() != it; ++it) {
            const call_graph_node* const caller =
                get_call_graph_node(*it);
            if (find(path.begin(), path.end(), *it) != path.end()) {
                if (debug_os) {
                    *debug_os << " R " << caller->first <<
                        " " << func->first << "\n";
                }
                continue;
            }
            path.push_back(caller);
            find_roots(graph, path_include, path_exclude, path, os, found_flag,
                stop_at_include_flag);
            path.pop_back();
            traversed_callers++;
        }
    }
    if (0 < traversed_callers || ! found_flag || path.size() <= 1) {
        return;
    }
    const char* sep = "";
    for (call_path::const_iterator
            it = path.end(); path.begin() != it; ) {
        --it;
        os << sep << (*it)->first;
        sep = "/";
    }
    os << "\n";
}

// Bypass input stream with rtl_parse, as on mac cin.read appears to terribly
// inefficient at the moment.
class file_reader
{
public:
    explicit file_reader(
        const char* name)
        : m_fd(::open(name, O_RDONLY)),
          m_err(m_fd < 0 ? errno : 0),
          m_count(0)
        {}
    explicit file_reader(
        int fd)
        : m_fd(fd),
          m_err(0)
        {}
    ~file_reader()
        { file_reader::close(); }
    void close()
    {
        if (0 <= m_fd) {
            if (::close(m_fd)) {
                m_err = errno;
            }
            m_fd = -1;
        }
    }
    bool read(
        void*      ptr,
        streamsize size)
    {
        if (bad()) {
            return false;
        }
        const ssize_t nrd = ::read(m_fd, ptr, size);
        if (nrd < 0) {
            m_err = errno;
        } else {
            m_count = nrd;
        }
        return (0 < nrd);
    }
    bool bad() const
        { return (m_fd < 0 || 0 != m_err); }
    streamsize gcount() const
        { return m_count; }
    int get_error() const
        { return m_err; }
private:
    int        m_fd;
    int        m_err;
    streamsize m_count;
private:
    file_reader(
        const file_reader&);
    file_reader& operator=(
        const file_reader&);
};

class insert_edge
{
public:
    insert_edge(
        reverse_call_graph& graph)
        : m_graph(graph),
          m_calls_count(0)
        {}
    template<typename T>
    void operator()(
        const T& caller,
        const T& func)
    {
        if (func != caller) {
            m_graph.insert(call_graph_node(func, func_callers())
                ).first->second.push_back(&*m_graph.insert(
                    call_graph_node(caller, func_callers())).first);
            m_calls_count++;
        }
    }
    int get_calls_count() const
        { return m_calls_count; }
private:
    reverse_call_graph& m_graph;
    int                 m_calls_count;
private:
    insert_edge(
        const insert_edge&);
    insert_edge& operator=(
        const insert_edge&);
};

template<typename ST>
class display_edge
{
public:
    explicit display_edge(
        ST& os)
        : m_os(os)
        {}
    template<typename T>
    void operator()(
        const T& caller,
        const T& call) const
        { m_os << caller << "/" << call << "\n"; }
private:
    ST& m_os;
private:
    display_edge(
        const display_edge&);
    display_edge& operator=(
        const display_edge&);
};

typedef std::map<string, string>            demangle_dict;
typedef std::map<string, std::set<string> > calls_dict;
typedef calls_dict                          refs_dict;

    static void
rtl_make_graph(
    demangle_dict       demangle,
    calls_dict          calls,
    refs_dict           refs,
    reverse_call_graph& graph)
{
    if (debug_os) {
        display_edge<ostream> func(*debug_os);
        for_each_edge_demangle(func, demangle, calls, refs);
    }
    insert_edge edge_inserter(graph);
    for_each_edge_demangle(edge_inserter, demangle, calls, refs);
    cerr << "functions: " << graph.size() <<
        " calls: " << edge_inserter.get_calls_count() << "\n";
}

    static int
rtl_load_from_list(
    reverse_call_graph& graph,
    const char*         file_name,
    bool                include_refs_flag,
    ostream&            oerr)
{
    ifstream file;
    if (file_name) {
        file.open(file_name);
    }
    istream& is = file_name ?
        static_cast<istream&>(file) :
        static_cast<istream&>(std::cin);
    if (! is) {
        cerr << (file_name ? file_name : "") << ": " << strerror(errno) << "\n";
        return 1;
    }
    demangle_dict demangle;
    calls_dict    calls;
    refs_dict     refs;
    int           files = 0;
    int           ret   = 0;
    string        line;
    line.reserve(1024);
    while (getline(is, line)) {
        if (line.empty()) {
            continue;
        }
        file_reader reader(line.c_str());
        if (reader.bad()) {
            cerr << line << ": " << strerror(reader.get_error()) << "\n";
            ret = 1;
            continue;
        }
        if (rtl_parse(reader, cerr, demangle, calls, refs, include_refs_flag,
                debug_os)) {
            ret = 1;
        }
        files++;
    }
    file.close();
    cerr << "files: " << files << " ";
    cerr.flush();
    rtl_make_graph(demangle, calls, refs, graph);
    return ret;;
}

    static int
rtl_load(
    reverse_call_graph& graph,
    const char*         file_name,
    bool                include_refs_flag,
    ostream&            oerr)
{
    demangle_dict demangle;
    calls_dict    calls;
    refs_dict     refs;
    int           ret = 0;
    if (! file_name) {
        file_reader reader(0);
        ret = rtl_parse(reader, cerr, demangle, calls, refs, include_refs_flag,
            debug_os);
    } else {
        file_reader reader(file_name);
        if (reader.bad()) {
            cerr << file_name << ": " << strerror(reader.get_error()) << "\n";
            ret = 1;
        }
        if (rtl_parse(reader, cerr, demangle, calls, refs, include_refs_flag,
                debug_os)) {
            ret = 1;
        }
    }
    rtl_make_graph(demangle, calls, refs, graph);
    return ret;
}

    static int
load_list(
    const reverse_call_graph& graph,
    const char*               file_name,
    path_filter&              filter)
{
    ifstream stream(file_name);
    if (! stream) {
        const int err = errno;
        cerr << file_name << ": " << strerror(err) << "\n";
        return 1;
    }
    string line;
    while (getline(stream, line)) {
        size_t pos;
        for (pos = 0; pos < line.size() && (line[pos] & 0xFF) <= ' '; pos++)
            {}
        if (0 < pos) {
            line.erase(0, pos);
        }
        if (line.empty()) {
            continue;
        }
        for (pos = line.size() - 1; 0 < pos && (line[pos] & 0xFF) <= ' '; pos--)
            {}
        if (++pos < line.size()) {
            line.erase(pos);
        }
        reverse_call_graph::const_iterator const it = graph.find(line);
        if (graph.end() == it) {
            cerr << line << ": not found\n";
            continue;
        }
        filter.insert(&*it);
    }
    return 0;
}

} // namespace

    int
main(
    int    argc,
    char** argv)
{
    const string debug_opt("-d");
    const string include_opt("-i");
    const string include_reset_opt("-ic");
    const string exclude_opt("-e");
    const string exclude_reset_opt("-ec");
    const string include_list_opt("-il");
    const string exclude_list_opt("-el");
    const string stop_at_include_opt("-si");
    const string continue_at_include_opt("-ci");
    const string load_egypt_opt("-egypt");
    const string load_rtl_list_opt("-rtll");
    const string load_np_refs_opt("-no-refs");
    bool         rtl_flag(true);
    bool         rtl_list_flag(false);
    bool         include_refs_flag(true);
    int          i;

    for (i = 1; i < argc; ++i) {
        if (argv[i] == debug_opt) {
            debug_os = &cerr;
        } else if (argv[i] == load_egypt_opt) {
            rtl_flag = false;
        } else if (argv[i] == load_rtl_list_opt) {
            rtl_list_flag = true;
            rtl_flag      = true;
        } else if (argv[i] == load_np_refs_opt) {
            include_refs_flag = false;
        } else {
            break;
        }
    }
    if (argc <= i || string("-h") == argv[i] || string("--help") == argv[i]) {
        cerr << "Usage: " << argv[0] <<
            " [options] function1 function2 ... < rtl-input\n"
            " [-d]          -- debug, prints into"
                " standard error all graph edges (unless invoked with -egypt)"
                " and include / exclude processing\n"
            " [-egypt]      -- Graphviz input format created by egypt script."
                " Default is rtl format created by gcc -fdump-rtl-expand\n"
            " [-rtll]       -- standard in is list of rtl file names, one file"
                " name per line, instead of rtl input\n"
            " [-no-refs]    -- produce direct call graph, by not including"
                " functions references when parsing"
                " rtl (passing / assigning function addresses)\n"
            " The prior options control reverse call graph construction.\n"
            " These options must placed before the following options that"
            " control graph traversal.\n"
            " [-i function] -- include call paths with functions names\n"
            " [-e function] -- exclude call paths with functions names\n"
            " [-ic]         -- clear include functions list\n"
            " [-ec]         -- clear exclude functions list\n"
            " [-il]         -- file with list of include functions, one function"
                " name per line\n"
            " [-el]         -- file with list of exclude functions, one function"
                " name per line\n"
            " [-si]         -- stop traversal if matches function name in"
                " include list (default); has effect only if include list is"
                " no empty; call path with excluded functions that occur in the"
                " path before include functions will not be excluded / filtered"
                " out\n"
            " [-ci]         -- continue traversal if matches include function\n"
            " With -egypt the input is the output of \"egypt\" perl script"
            " which converts files created by gcc -fdump-rtl-expand into"
            " Graphviz input format.\n"
            " The output is call paths for the specified functions / methods.\n"
            " A practical invocation example:\n"
            " find path_to_build_directory -type f -name '*.expand' | " <<
                argv[0] << " -rtll function1 function2\n"
        ;
        return 1;
    }
    int                ret = 0;
    reverse_call_graph graph;
    if (rtl_flag) {
        if (rtl_list_flag) {
            ret = rtl_load_from_list(graph, 0, include_refs_flag, cerr);
        } else {
            ret = rtl_load(graph, 0, include_refs_flag, cerr);
        }
    } else {
        load(graph, std::cin);
    }
    path_filter path_include;
    path_filter path_exclude;
    bool        stop_at_include_flag = true;
    call_path   path;
    path.reserve(1 << 7);
    for ( ; i < argc; ++i) {
        bool include_flag = false;
        bool exclude_flag = false;
        if (include_opt == argv[i]) {
            if (argc <= ++i) {
                break;
            }
            include_flag = true;
        } else if (exclude_opt == argv[i]) {
            if (argc <= ++i) {
                break;
            }
            exclude_flag = true;
        } else if (include_reset_opt == argv[i]) {
            path_include.clear();
            continue;
        } else if (stop_at_include_opt == argv[i]) {
            stop_at_include_flag = true;
            continue;
        } else if (continue_at_include_opt == argv[i]) {
            stop_at_include_flag = false;
            continue;
        } else if (exclude_reset_opt == argv[i]) {
            path_exclude.clear();
            continue;
        } else if (include_list_opt == argv[i]) {
            if (argc <= ++i) {
                break;
            }
            if (load_list(graph, argv[i], path_include)) {
                ret = 1;
            }
            continue;
        } else if (exclude_list_opt == argv[i]) {
            if (argc <= ++i) {
                break;
            }
            if (load_list(graph, argv[i], path_exclude)) {
                ret = 1;
            }
            continue;
        }
        reverse_call_graph::const_iterator const it = graph.find(argv[i]);
        if (graph.end() == it) {
            cerr << argv[i] << ": not found\n";
            ret = 1;
            continue;
        }
        if (include_flag) {
            path_include.insert(&*it);
            continue;
        }
        if (exclude_flag) {
            path_exclude.insert(&*it);
            continue;
        }
        path.push_back(&*it);
        find_roots(graph, path_include, path_exclude, path, std::cout,
            path_include.empty(),
            stop_at_include_flag && ! path_include.empty());
        path.clear();
    }
    return ret;
}
