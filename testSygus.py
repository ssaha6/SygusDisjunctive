from sygus import *
import sys
from pprint import pprint
import time
import random
import operator as op
from functools import reduce


def ncr(n, r):
    r = min(r, n-r)
    numer = reduce(op.mul, range(n, n-r, -1), 1)
    denom = reduce(op.mul, range(1, r+1), 1)
    return int(numer / denom)
    

def learnHoudiniString(strFeatures, strFeatureVectors):
    
    workList = {key: True for key in range(0, len(strFeatures))}
    for idx in range(0, len(strFeatures)):
        for vector in strFeatureVectors:
            if vector[idx] == "false":
                workList[idx] = False
    
    terms = []
    for idx in range(0, len(strFeatures)):
        if workList[idx]:
            terms.append(strFeatures[idx])
    return terms


def small_tests():
    solver1 = SygusDisjunctive(
                    ["cond1", "cond2", "cond3", "cond4", "eq1", "eq2", "eq3"],
                    
                    [["true", "false", "true", "true","true", "false", "true"],
                    ["true", "true", "true", "true","false", "false", "false"]],
                    
                    k=2,
                    cdt="true"
                )
    
    output_tree = solver1.run_sygus()
    print(output_tree)
    
    t = "true"
    f = "false"
    
    solver2 = SygusDisjunctive(
                        ["cp1", "cp2", "cp3", "ep1", "ep2", "ep3"],

                        [[t,t,f,t,t,f],
                        [f,t,f,t,t,f],
                        [f,f,t,t,f,f],
                        [t,f,f,t,f,t]
                        ],
                    
                        k = 1,
                        cdt = "c1" # no soln
                        # cdt = "true" # (ite  c2 * * )
                     )
    output_tree = solver2.run_sygus()
    print(output_tree)
    
    solver3 = SygusDisjunctive(
                        ["cp1", "cp2", "cp3", "ep1", "ep2", "ep3"],

                        [[t,t,f,t,t,f],
                        [f,t,f,t,t,f],
                        [f,f,t,t,f,f],
                        [t,f,f,t,f,t]
                        ],
                
                        k = 1,
                        #  cdt = "c1" # no soln
                        cdt = "true" # (ite  c2 * * )
                     )
    output_tree = solver3.run_sygus()
    print(output_tree)
    
    solver4 = SygusDisjunctive(
                        ['c1', "c2", "c3", "c4", "c5", 'e1', 'e2', 'e3', 'e4', 'e5', 'e6'],
                        
                        [[t,f,t,t,t,f,t,f,f,t,t],
                         [t,t,f,t,f,f,t,t,f,f,f],
                         [t,t,t,f,f,t,t,f,f,f,t]
                        ], 
                        
                        k = 1,
                        cdt = "true"
    )
    
    output_tree = solver4.run_sygus()
    print(output_tree)
    
    
    solver5 = SygusDisjunctive( 
                        ["c1", "c2", "e1", "e2", "e3"],
        
                        [[t,f,t,t,f],
                         [f,f,t,f,t],
                        ],
                        
                        k = 1,
                        cdt = "true"
    )
    
    output_tree = solver5.run_sygus()
    print(output_tree)
    
    solver6 = SygusDisjunctive(
        ['cond7', 'cond6', 'cond5', 'cond4', 'cond3', 'cond1', 'cond0'],

        [['false', 'false', 'false', 'true', 'false', 'true', 'false'],
        ['true', 'true', 'false', 'false', 'true', 'true', 'false'],  
        ['true', 'true', 'false', 'false', 'true', 'false', 'true'], 
        ['true', 'true', 'true', 'false', 'false', 'true', 'false'], 
        ['true', 'true', 'true', 'false', 'false', 'true', 'false']],
        k = 3,
        cdt = "(ite cond1 (ite cond5 (and cond7 cond6 cond5 cond1) (and cond1) ) (ite cond5 (and cond7 cond6 cond5 cond4 cond3 cond1 cond0) (and cond7 cond6 cond3 cond0) ) )"
    )
    output_tree = solver6.run_sygus()
    print(output_tree)
    
def large_test(strFeature, strFeatureVectors45):
    output = learnHoudiniString(strFeature,strFeatureVectors45)
    solver45  = SygusDisjunctive(
        strFeature,
        strFeatureVectors45,
        k = 2,
        cdt = "(and " + " ".join(output) + " )"
        )
    start_time = time.time()
    print(solver45.run_sygus())
    elapsed_time = time.time() - start_time
    print("%02d:%02d:%02d" % (elapsed_time // 3600, (elapsed_time % 3600 // 60), (elapsed_time % 60 // 1)))
    
def large_sample_breakdown(strFeature, strFeatureVectors45):
    
    for l in range(36,len(strFeatureVectors45)):
        print("size = ", l, " ======================================")
        
        for _ in range(0,min(100, ncr(len(strFeatureVectors45), l))):
            indexes = sorted(random.sample(range(0,len(strFeatureVectors45)), l))
            print(indexes)
                
            new_sample = [strFeatureVectors45[x] for x in indexes]
            
            output = learnHoudiniString(strFeature,new_sample)
            print(output)
            sys.stdout.flush()
            
            solver1  = SygusDisjunctive(
                strFeature,
                new_sample,
                k = 1,
                cdt = "(and " + " ".join(output) + " )"    #"true"
                )
            
            start_time = time.time()
            output_tree = solver1.run_sygus()
            elapsed_time = time.time() - start_time
            if output_tree:
                print("soln-found")
            else: 
                print("not-found")
            print("%02d:%02d:%02d" % (elapsed_time // 3600, (elapsed_time % 3600 // 60), (elapsed_time % 60 // 1)))
            print("-----------------------------------")
                
    with open("output.txt", 'r') as f:
        contents = f.read()
        for num_contents in contents.split("======================================"):
            print(num_contents.count("not-found"), num_contents.count("soln-found") )
        
def large_sample_cdt(strFeature, strFeatureVectors45):
    
    output = learnHoudiniString(strFeature,strFeatureVectors45)
    # for l in [2]:
    for l in range(len(output), 0, -1):
        for comb in combinations(output, l):
            print(comb)
            solver1  = SygusDisjunctive(
                strFeature,
                strFeatureVectors45,
                k = 1,
                cdt = "(and " + " ".join(comb) + " )"    #"true"
                )
            start_time = time.time()
            output_tree = solver1.run_sygus()
            elapsed_time = time.time() - start_time
            print("%02d:%02d:%02d" % (elapsed_time // 3600, (elapsed_time % 3600 // 60), (elapsed_time % 60 // 1)))
            if output_tree:
                print("found")
    
    
    
def main(): 
    
    small_tests() 
    
    strFeature = ["cond0", "cond1", "cond2", "cond3", "cond4", "cond5", "cond6", "cond7", "cond8", "cond9", "cond10", "cond11", "cond12", "cond13", "cond14", "cond15", "cond16", "cond17", "cond18", "cond19", "cond20", "cond21", "cond22", "cond23", "cond24", "cond25", "cond26", "cond27", "cond28", "cond29", "cond30", "cond31", "cond32", "cond33", "cond34", "cond35", "cond36", "cond37", "cond38", "cond39", "cond40", "cond41", "cond42", "cond43", "cond44", "cond45", "cond46", "cond47", "cond48", "cond49", "cond50", "cond51", "cond52", "cond53", "cond54", "cond55", "cond56", "cond57", "cond58", "cond59", "cond60", "cond61", "cond62", "cond63", "cond64", "cond65", "cond66", "cond67", "cond68", "cond69", "cond70", "cond71", "cond72", "cond73", "cond74", "cond75", "cond76", "cond77", "cond78", "cond79", "cond80", "cond81", "cond82", "cond83", "cond84", "cond85", "cond86", "cond87", "cond88", "cond89", "cond90", "cond91", "cond92", "cond93", "cond94", "cond95", "cond96", "cond97", "cond98", "cond99", "cond100", "cond101", "cond102", "cond103", "cond104", "cond105", "cond106", "cond107", "cond108", "cond109", "cond110"]
    strFeatureVectors45 = [
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false'],
            ['true', 'true', 'true', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'false', 'false', 'false', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true'],
            ['false', 'true', 'true', 'true', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'true', 'true', 'false', 'false', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'true', 'false', 'false', 'true', 'false', 'true', 'false', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'true', 'true', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true', 'false', 'false', 'false', 'true', 'true', 'true'],
            ]
    
    
    large_test(strFeature, strFeatureVectors45)
    
    large_sample_breakdown(strFeature, strFeatureVectors45)
    
    large_sample_cdt(strFeature, strFeatureVectors45)




main()
