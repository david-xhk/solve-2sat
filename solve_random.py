#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
2D Challenge 50.004: Introduction to Algorithms Sept-Dec 2019 term

2-SAT Solver in Polynomial Time

Bonus Implementation: Random Walk Solver

Created on Sun Nov 10 18:23:13 2019

@author: HKXIE
"""

import io, time, random


class My2SATSolver:
    """2-SAT solver based on random walk."""        
    
    test_cases = []  
    
    class TestCase:
        def __init__(self):
            self.name = None
            self.num_vars = None
            self.num_clauses = None
            self.is_sat = None
            self.time_taken = None
            self.num_steps = None
            self.assignments = None
    
    
    @staticmethod
    def print_cases():
        for test_case in My2SATSolver.test_cases:
            print(test_case.num_vars,
                  test_case.num_clauses,
                  test_case.is_sat,
                  test_case.time_taken,
                  test_case.num_steps,
                  sep=",")
    
        
    @staticmethod
    def solve(cnf):
        """
        Solve a 2-SAT problem.
        
        Uses strongly-connected components to find satisfiability.
        
        Input: str (cnf text) OR file object (cnf file)
        """
        test_case = My2SATSolver.TestCase()
        result = My2SATSolver.parse_cnf(cnf)
        if not result:  # failed to parse, return None
            return None
        var, clauses = result
        test_case.num_vars = len(var)
        test_case.num_clauses = len(clauses)
        
        start_time = time.time()  # start timing here
        
        result = My2SATSolver.random_walk(var, clauses)
        
        end_time = time.time()  # stop timing here
        
        test_case.num_steps = result["num_steps"]
        
        time_taken = end_time-start_time
        test_case.time_taken = time_taken
        
        if result["result"] in ("UNSAT", "TIMEOUT"):
            print("FORMULA UNSATISFIABLE")
        else:
            print("FORMULA SATISFIABLE")

        test_case.is_sat = result["result"]
        
        # sort assignments by increasing order
        assignments = result["assignments"]
        assignments = {k:assignments[k] for k in sorted(assignments)}

        test_case.assignments = assignments
        
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
    def parse_cnf(cnf):
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
    def random_walk(var, clauses, k=100, timeout=60):
        assignments = dict.fromkeys(var, 0)
        
        def calculate_truth(clause):
            for literal in clause:
                if literal > 0:
                    if assignments[literal] == 1:
                        return 1
                elif assignments[-literal] == 0:
                    return 1
            return 0
        
        def flip(literal):
            assignments[abs(literal)] = 1-assignments[abs(literal)]
        
        num_var = len(var)
        is_timeout = False
        start_time = time.time()
        for num_steps in range(k*num_var**2):
            if time.time()-start_time > timeout:  # check for timeout
                is_timeout = True
                break
            is_unsat = False  # reset flag
            for clause in clauses:  # find a bad clause
                if calculate_truth(clause) == 0:
                    is_unsat = True
                    bad_clause = clause
                    break
            if is_unsat:  # choose a random literal
                if len(bad_clause) == 1:
                    literal = bad_clause[0]
                elif random.random() > 0.5:
                    literal = bad_clause[0]
                else:
                    literal = bad_clause[1]
                flip(literal)  # and flip it
            else:
                break
        
        result = {"num_steps":num_steps+1}
        if not is_unsat:
            result["assignments"] = assignments
            result["result"] = "SAT"
        else:
            result["assignments"] = {}
            if is_timeout:
                result["result"] = "TIMEOUT"
            elif is_unsat:
                result["result"] = "UNSAT"
        return result


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


def create_graph(txt):
    graph = {}
    for line in txt.split("\n"):
        node, *successors = [int(s) for s in line.split(" ") if s]
        graph[node] = successors
    return graph
