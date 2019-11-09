#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
2D Challenge 50.004: Introduction to Algorithms Sept-Dec 2019 term

2-SAT Solver in Polynomial Time

Using Essentially a DFS Algorithm

With Bonus Implementation: Randomizing Algorithm

Created on Sat Nov  9 11:22:22 2019

@author: HKXIE
"""

import io, time


class My2SATSolver:
    """
    2-SAT solver based on strongly-connected components of implication graphs.
    
    Based on Tarjan's algorithm to find strongly-connected components.
    """    

    test_cases = []  
    
    class TestCase:
        def __init__(self):
            self.name = None
            self.num_vars = None
            self.num_clauses = None
            self.is_sat = None
            self.time_taken = None
            self.assignments = None
    
    
    @staticmethod
    def print_cases():
        for test_case in My2SATSolver.test_cases:
            print(test_case.num_vars,
                  test_case.num_clauses,
                  test_case.is_sat,
                  test_case.time_taken,
                  sep=",")
    
    
    @staticmethod
    def solve(cnf):
        """
        Solve a 2-SAT problem.
        
        Uses strongly-connected components to find satisfiability.
        
        Input: str (cnf text) OR file object (cnf file)
        """
        test_case = My2SATSolver.TestCase()
        result = My2SATSolver.parse_clauses(cnf)
        if not result:  # failed to parse, return None
            return None
        var, clauses = result
        test_case.num_vars = len(var)
        test_case.num_clauses = len(clauses)
        
        start_time = time.time()  # start timing here
        graph = My2SATSolver.parse_graph(clauses)
        sccs = My2SATSolver.tarjan_scc(graph)
        
        assignments = {}
        for scc in sccs:
            for node in scc:
                if -node in scc:  # literal and its negation are present
                    print("FORMULA UNSATISFIABLE")
                    test_case.is_sat = "UNSAT"
                    end_time = time.time()
                    time_taken = end_time-start_time
                    test_case.time_taken = time_taken
                    print("time taken: " + format_time(time_taken))
                    return test_case
                if node not in assignments:  # assign the literal to true
                    assignments[node] = 1
                    assignments[-node] = 0  # and its negation to false
        
        end_time = time.time()  # stop timing here
        time_taken = end_time-start_time
        
        # sort assignments by increasing order, getting rid of negative literals
        assignments = {k:assignments[k] for k in sorted(assignments) if k > 0}
        
        test_case.is_sat = "SAT"
        test_case.time_taken = time_taken
        test_case.assignments = assignments
        
        print("FORMULA SATISFIABLE")  # print outputs
        print_long(" ".join(map(str, assignments.values())))
        print("time taken: " + format_time(time_taken))
        
        return test_case
    
    
    @staticmethod
    def solve_all(*cnf_paths):
        """
        Solve all provided 2-SAT problems one by one.
        
        Input: str (any number of .cnf file paths)
        """
        My2SATSolver.test_cases.clear()
        for cnf_path in cnf_paths:
            with open(cnf_path, "r") as f:
                cnf_name = cnf_path.rsplit("/", 1)[1]
                print("solving " + cnf_name)
                test_case = My2SATSolver.solve(f)
                test_case.name = cnf_name
                My2SATSolver.test_cases.append(test_case)
                print()
    
    
    @staticmethod
    def parse_clauses(cnf):
        """
        Takes in cnf file and outputs its set of clauses.
        
        Input:  str (cnf text) OR file object (cnf file)
        Output: list of 1-tuples or 2-tuples [(a,), (b,c), ...]
        """
        num_var = 0
        num_clause = 0
        var = []
        fmt = None
        clauses = []
        
        if isinstance(cnf, io.TextIOBase):
            lines = cnf
        
        elif isinstance(cnf, str):
            lines = cnf.splitlines()
        
        for i, line in enumerate(lines):        
            if fmt != "cnf":
                if line.startswith("c"):  # preamble
                    continue
                
                if not line.startswith("p"):
                    print("invalid problem statement")
                    return None
                
                else:
                    try:  # problem statement
                        _, fmt, num_var, num_clause = line.split()
                    except ValueError:
                        print("invalid problem statement")
                        return None
                    if fmt != "cnf":
                        print("only support cnf format")
                        return None
                    try:
                        num_var = int(num_var)
                    except ValueError:
                        print("invalid number of variables")
                        return None
                    try:
                        num_clause = int(num_clause)
                    except ValueError:
                        print("invalid number of clauses")
                        return None
            
            elif line in ("", "\n"):
                continue
            
            else:  # clauses
                try:
                    *b, z = line.split()
                except ValueError:
                    print("error at line " + str(i+1) + ": '" + line + "'")
                    return None
    
                if z != "0":
                    print("clause at line " + str(i+1) + 
                          " ends with invalid character " + str(z) +
                          ", expected 0")
                    return None
                
                if len(b) == 0:
                    print("empty clause at line " + str(i+1))
                    print("FORMULA UNSATISFIABLE")
                    return None
                
                if len(b) > 2:
                    print("line " + str(i+1) + "has " + str(b) + " literals, " +
                          "expected <= 2 literals in 2-SAT problem")
                    return None
                
                else:
                    for i in range(len(b)):
                        try:
                            b[i] = int(b[i])
                        except ValueError:
                            print("invalid literal at line " + str(i+1) + ": " +
                                  str(b[0]) + ", expected an integer")
                            return None
                        if abs(b[i]) not in var:
                            var.append(abs(b[i]))
                    if len(b) == 1:
                        clauses.append((b[0],))
                    else:
                        clauses.append((b[0], b[1]))
        
        if num_var != len(var):
            print("stated " + str(num_var) + " but gave " + 
                  str(len(var)) + " variables. missing:")
            print_long(" ".join(str(i) for i in range(1, num_var+1) 
                           if i not in var),
                       max_lines=1, indent=2)
        
        if num_clause != len(clauses):
            print("stated " + str(num_clause) + " but gave " + 
                  str(len(clauses)) + " clauses")

        return var, clauses
        
    
    @staticmethod
    def parse_graph(clauses):
        """
        Takes in a set of clauses and outputs the adjacency list 
        of the implication graph which can be formed with the clauses.
        
        Input: list of 1-tuples or 2-tuples [(a,), (b,c), ...]
        Output: dict of int mapped to list of int {a:[b], c:[d,e], ...}
        """
        graph = {}
        
        for clause in clauses:
            if len(clause) == 2:
                a, b = clause
            else:  # length 1
                a = b = clause[0]
            
            if -a not in graph:  # initialize adjacency list of node
                graph[-a] = []
            if b not in graph[-a]:  # prevent duplicate successors
                graph[-a].append(b)
            
            if -b not in graph:
                graph[-b] = []
            if a not in graph[-b]:
                graph[-b].append(a)
            
        return graph
    
    
    @staticmethod
    def tarjan_scc(graph):
        """
        Tarjan's Algorithm (named for its discoverer, Robert Tarjan) is a 
        graph theory algorithm for finding the strongly connected components
        of a graph.
        
        Based on: http://www.logarithmic.net/pfh/blog/01208083168
        """
        # initialize variables
        index_ctr = [0]
        lowlinks = {}
        index = {}
        stack = []
        sccs = [] 
                
        def DFS_visit(node):      
            index[node] = index_ctr[0]
            lowlinks[node] = index_ctr[0] # initialize lowlink to index
            index_ctr[0] += 1
            stack.append(node)
            
            try:
                successors = graph[node]
            except:
                successors = []
            
            for successor in successors:
                # tree edge: visit and update lowlinks
                if successor not in lowlinks:
                    DFS_visit(successor)
                    lowlinks[node] = min(lowlinks[node],lowlinks[successor])
                
                 # back edge: don't visit, but compare its index with lowlink
                elif successor in stack:
                    lowlinks[node] = min(lowlinks[node],index[successor])
                
                # cross edge: ignore. move on to next successor
                else:
                    continue
                    
            # root node to SCC found. pop SCC off stack.
            if lowlinks[node] == index[node]:
                scc = []
                
                while True:
                    successor = stack.pop()
                    scc.append(successor)
                    if successor == node: break
                
                sccs.append(tuple(scc))
        
        # visit all unvisited nodes
        for node in graph:
            if node not in lowlinks:
                DFS_visit(node)
        
        return sccs


def format_time(time_taken):
    units = ["s", "ms", "μs", "ns", "ps"]
    i = 0
    while time_taken < 0.01:
        time_taken *= 1e3
        i += 1
        if i == len(units)-1:
            break
    return str(round(time_taken, 8)) + units[i]


def print_long(txt, max_length=50, max_lines=2, dots=2, rlen=10, indent=0):
    words = txt.split()
    lines = []
    for i in range(max_lines):
        line = " "*indent
        while len(line) < max_length:
            try:
                word = words.pop(0)
            except:
                break
            if len(word) > max_length:
                line = word[:max_length-1]+"-"
                words.insert(0, word[max_length-1:])
            elif len(line) + len(word) > max_length:
                words.insert(0, word)
                break
            else:
                line += word + " "
        lines.append(line.rstrip())
    if words:
        last_word = words.pop()
        if len(last_word) > max_length:
            last_word = last_word[-rlen:]
        while True:
            new_last_word = words.pop() + " " + last_word
            if len(new_last_word) > rlen: 
                break
            else:
                last_word = new_last_word
        last_word = " " + last_word
        last_sentence = lines[-1]
        while len(last_sentence) > max_length-len(last_word)-dots:
            if " " in last_sentence:
                last_sentence = last_sentence.rsplit(" ", 1)[0]
            else:
                last_sentence = last_sentence[:-1]
        lines[-1] = last_sentence+"."*dots+last_word
    for line in lines:
        if line:
            print(line.ljust(max_length))


def parse_graph(txt):
    graph = {}
    for line in txt.split("\n"):
        node, *successors = [int(s) for s in line.split(" ") if s]
        graph[node] = successors
    return graph
