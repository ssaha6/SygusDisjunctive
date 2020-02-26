from  command_runner import runCommand
import re
import sys


distcintConditionals = True

class Nd:
    def __init__(self):
        self.data = None
        self.left = None
        self.right = None
    
    def __str__(self, sample):
        if not self.left and not self.right:
            return "*"
            parentnode = self.parent
            conjunct = []
            while parentnode != None:
                conjunct = conjunct.append(parentnode.data)
                parentnode = parentnode.parent
            
            return houdini(conjunct, sample)
        
        else:
            return " ".join(["(ite ", str(self.data, sample),str(self.right, sample),  str(self.left, sample), ")"])
    
class Node(Nd):
    def __init__(self):
        super().__init__()
        # self.selectme_history = [] 
        # self.selectme_current = []
        self.selectme = []
        self.k = None
        self.index = None
        self.constraint = None
    

class SygusDisjunctive:
    def __init__(self, pred_names, pred_data,  k, cdt="true"):
        self.cond_pred = pred_names
        self.cond_pred_data = pred_data
        
        assert(k>0)
        self.k = k
        
        self.cdt = cdt
        self.dp_trees = {} 
        self.all_trees = self.generate_all_trees(k)
        
        self.pvariables = {}
        self.pvariablesCall = {}
        self.allpvariables = []
        self.allpvariablesCall = []

        for k_itr in range(self.k):
            self.pvariables[k_itr] = []
            self.pvariablesCall[k_itr] = []
            for p_itr in self.cond_pred:
                self.pvariables[k_itr].append('p_'+str(k_itr) + '_' + p_itr)
                self.pvariablesCall[k_itr].append('( p_'+str(k_itr) + '_' + p_itr + " true )")
                self.allpvariables.append('p_'+str(k_itr) + '_' + p_itr)
                self.allpvariablesCall.append('( p_'+str(k_itr) + '_' + p_itr + " true )")
        
        self.wvariables = [] 
        self.uvariables = []
        for pred  in self.cond_pred: 
            self.wvariables.append('w_'+pred)
            self.uvariables.append('u_'+pred)
        
        self.wvariablesCall = []
        for p in self.wvariables:
            self.wvariablesCall.append("( " + p + " true )")
        
        self.p_count=0
        self.q_count=0  
    
    
    def generate_all_trees(self, k):
        
        if k in self.dp_trees:
            return self.dp_trees[k]
        
        if k == 0 :
            self.dp_trees[k] = [[""]]
        # elif k == 1:
        #     self.dp_trees[k] = [["0", "1"]]
        
        else: 
            trees = []
            for i in range(0, k):
                for trl in self.append_tree("0",self.generate_all_trees(i)):
                    for trr in self.append_tree("1", self.generate_all_trees(k-1-i)):
                        combined = sorted(trl + trr, key=lambda x: (len(x),x))
                        trees.append(combined)
            
            self.dp_trees[k] = trees #sorted(trees, key=lambda x: (len(x),x))
            
        return self.dp_trees[k]
        
    def append_tree(self, prefix, list_trees):
        res = []
        for tree in list_trees:
            tr = list(map(lambda y: prefix+y, tree))
            res.append(tr)
        return res
    
    
    def zip_column(self, *argv):  
        result = [] 
        
        length = 1
        for arg in argv:  
            if isinstance(arg, list):
                if length == 1:
                    length = len(arg)
                else: 
                    assert( len(arg) == length)
        
        for itr in range(length):
            row = ""
            for arg in argv: 
                if isinstance(arg, str):
                    row+= " " + arg + " "
                elif isinstance(arg, int):
                    row+= " " + str(arg) + " "  
                elif isinstance(arg, list):
                    if isinstance(arg[itr], str):
                        row += " " + arg[itr] + " "
                    elif isinstance(arg[itr], int):
                        row += " " + str(arg[itr]) + " "
                    elif isinstance(arg[itr], list):
                        for element in arg[itr]:
                            if isinstance(element, str):
                                row+= " " + element + " "
                            elif isinstance(element, int):
                                row += " " + str(element) + " " 
                    
                    # row += 
                    # row += ''.join(list(map(lambda x: str(x) if isinstance(x,int) else x, arg[itr])))
            
            result.append(row)
        return result
    
    
    
    def set_logic(self, logic ="BV"):
        ret = "( set-logic " + logic + " )\n"
        # ret += "(define-fun ite ((b1 Bool)(b2 Bool)(b3 Bool)) Bool (or (and b1 b2) (and (not b1) b3))) \n "
        return ret
    
    def synth_conditionals(self):
        ret = ''
        for k, value in self.pvariables.items():
            ret += '\n'.join(self.zip_column('(synth-fun ', value, '((x Bool)) Bool ((Start Bool (true false)  )) )' )) + '\n'
        return ret
    
    def synth_witness(self):
        return '\n'.join(self.zip_column( '(synth-fun ', self.wvariables, '  ((x Bool)) Bool ((Start Bool (true false)  )) ) ' ))
    
    def declare_universal_variables(self):
        return '\n'.join(self.zip_column( '(declare-var ', self.uvariables,  ' Bool)'))
    
    def define_CDT(self):
        ret = "(define-fun cdt (" 
        ret +=  ' '.join([ "( " + x + " Bool)" for x in self.cond_pred])
        
        # ret += ") Bool \n " + self.cdt + "\n)\n"  
        # return ret
    
        ret += ") Bool \n"
        add = [] 
        for cond in self.cond_pred:
            if cond in self.cdt:
                add.append(cond)
            else: 
                add.append("(or " + cond + " (not " + cond + " ))")
            
        ret += self.make_and(add, delim="\n")
        ret +=  "\n)\n"  
        return ret
    
    def make_and(self, options, delim=" "):
        return self.make_overloading_op("and", options, delim)
    
    def make_or(self, options, delim=" "):
        return self.make_overloading_op("or", options, delim)
    
    def make_overloading_op(self, op, options, delim=" "):
        if not delim:
            delim = " "
        
        if len(options) > 2:
            ret = "(" + op + " "
            ret += ( delim + "(" + op + " ").join(options[:-1]) + delim  + options[-1] + delim + (")"*(len(options)-1))
            # ret += ")"
            return ret
        elif len(options) == 2:
            return "(" + op + " "  + ' '.join(options)   +  " )"
        elif len(options) == 1: 
            return options[0]
        elif len(options) == 0:
            return ""
    
    def generate_constraint(self):
        ret = []
        for k_itr in range(self.k):
            ret.append(self.make_or(self.pvariablesCall[k_itr]))
            
            #(=> p_1_cp2 (and ( not p_1_cp1) ( not p_1_cp3) ))
            for p_itr in range(len(self.pvariables[k_itr])):
                    ret.append("(=> " + self.pvariablesCall[k_itr][p_itr] + " " + \
                            self.make_and(list(map(lambda x: "( not " + x + ")", self.pvariablesCall[k_itr][0:p_itr] + self.pvariablesCall[k_itr][p_itr+1:]))) + " )")
        
        ret.append('( => ( eval ' + ' '.join(self.uvariables) + ' ' + ' '.join(self.allpvariablesCall) \
                              + ") (cdt " + ' '.join(self.uvariables) + "))")
                              
        ret.append("(cdt " + ' '.join(self.wvariablesCall) + ")")
        ret.append("(not (eval " + " ".join(self.wvariablesCall) + ' '.join(self.allpvariablesCall) +  " ))")
        
        
        if distcintConditionals:
            # add constraint if a predicate is chosen no other node can have that predicate
            # p_i_c => and (not p_j_c) 
            if self.k > 1:
                for p_itr in range(len(self.cond_pred)):
                    for i in range(self.k):
                        mk = [] 
                        for j in range(self.k):
                            if i == j:
                                continue
                            mk.append("(not ( p_" + str(j) + "_" + self.cond_pred[p_itr] + " true ))" )
                        ret.append("(=>  ( p_" + str(i) + "_" + self.cond_pred[p_itr] + " true ) " + self.make_and(mk) + " )")
        
        return "(constraint \n" + self.make_and(ret, delim ="\n") + "\n)\n"
    
    
    def generate_selectme_fn(self):
        ret = "(define-fun selectme (" 
        ret += ' '.join( ["( value_" + str(i) + " Bool)" for i in range(len(self.cond_pred))] #leafnodes
                        +["( p_i_" + str(i) + " Bool)" for i in range(len(self.cond_pred)) ]) #cond_predicates
        ret += ") Bool\n"
        
        ending = "" 
        for i in range(len(self.cond_pred)):
            ret+= "(ite  p_i_" + str(i) + " value_" + str(i) + "\n"
            ending += ")"
    
        ret += "false " + ending + "\n)\n"
        return ret
    
    def generate_static_file(self):
        return  str(
                    self.set_logic() + "\n"
                    + self.synth_conditionals() + "\n"
                    + self.synth_witness() + "\n"
                    + self.define_CDT() + "\n"
                    + self.declare_universal_variables() + "\n"
                    + self.generate_selectme_fn() + "\n"
                )
    
    
    
    def selectme_statement(self, k):
        selectme_list = []
        for s_i in range(len(self.cond_pred_data)):
            ret = " (selectme "
            end = "" 
            for p_itr in range(len(self.cond_pred)):
                    ret += " " + self.cond_pred_data[s_i][p_itr] + " "
                    end += " p_"+ str(k) + "_" + self.cond_pred[p_itr] + " "
            ret += end + ") "
            selectme_list.append(ret)

        return selectme_list
    
    
    def insert_leaf(self, root, index): 
        root_itr = root
        for dir in index: 
            if dir == "0":
                if not root_itr.left:
                    root_itr.left = Node() 
                root_itr = root_itr.left
            if dir == "1":
                if not root_itr.right:
                    root_itr.right = Node() 
                root_itr = root_itr.right
        root_itr.index = index
        return
    
    
    def label_tree(self, root):
        if not root.selectme:
            root.selectme = []
        
        if not root.left and not root.right:
            root.k = self.q_count
            self.q_count += 1
            
            implications = []
            for cond_itr in range(len(self.cond_pred)):
                imp = "(=> (not " + self.cond_pred[cond_itr] + " )\n"
                
                ands = [] 
                for itr in range(len(root.selectme[0])): 
                    ands.append(self.make_and( list(map(lambda x: x[itr], root.selectme))))
                
                imp += self.make_or(ands, delim="\n") + " )"
                implications.append(imp)
            
            root.constraint = self.make_and(implications, delim = "\n")
            
        
        else:
            root.k = self.p_count
            self.p_count += 1
            
            current_selectme = self.selectme_statement(root.k)
            
            root.left.selectme = root.selectme + [self.zip_column("(not ", current_selectme, ")")]
            root.right.selectme = root.selectme +  [current_selectme]
            
            
            root.constraint = "(selectme  " + " ".join(self.cond_pred) + " " + " ".join([x  for x in self.pvariables[root.k]]) + " )\n"
             
            self.label_tree(root.left )
            self.label_tree(root.right)
            
        return
    
    
    def tree_to_smt(self, node):
        if not node.left and not node.right:
            return node.constraint
        else:
            return "(ite\n" + node.constraint + "\n" + self.tree_to_smt(node.right) +  "\n" + self.tree_to_smt(node.left)  + ")\n"
    
    
    
    def generate_eval(self, root):
        pass
        ret= str("(define-fun eval (" + ' '.join(["( " + x + " Bool)" for x in self.cond_pred]) + ' '.join(["( " + str(x) + " Bool)" for x in self.allpvariables])
                                   + ") Bool\n")
        
        ret += self.tree_to_smt(root) + "\n)\n"
        return ret
    
    
    def run_solver(self, constraint):
        
        with open("sygus.sl", "w", newline='\n') as file:
            file.write(constraint)
        
        # output = runCommand(["./cvc4-2020-02-06-win64-opt.exe", "--sygus-out=sygus-standard",  "--lang=sygus2", "sygus.sl"]) #"--cegqi-si=none",
        # output =  runCommand(["wsl", "--sygus-out=sygus-standard",  "--lang=sygus2", "sygus.sl"]) #"--cegqi-si=none",
        
        sys.exit(0)
        # pwsl = Shell("wsl")
        # output = pwsl.runCommand('./EnumerativeSolver/bin/starexec_run_Default', 'sygus.s') + '\'')

        if output: 
            if "\r\nb" in output: 
                output = re.sub("\'?\\r\\nb\'?", "\n", output)

            valuation = re.findall('\s*\(define\-fun\s+(.*)\s+\(\s*\)\s+Bool\s+(.*)\s*\)', output) 
            if len(valuation) == 0:
                return None
            else:
                return valuation 
            
        return None
    
    
    def project_copy(self, root, predicates_chosen, parent = None):
        if not root:
            return None
        
        new_root = Nd()
        
        if not root.left and not root.right:
            new_root.data = "*"
            new_root.parent = parent
            # new_root.data = equalities_chosen[root.k]
            
            
        else:
            new_root.data = predicates_chosen[root.k]
            new_root.left = self.project_copy(root.left, predicates_chosen, new_root)
            new_root.right = self.project_copy(root.right, predicates_chosen, new_root)
            new_root.parent = parent
        return new_root
    
    
    def run_sygus(self):
        for tree in self.all_trees:
            
            root = Node() 
            for leaf_index in tree:
                self.insert_leaf(root, leaf_index)
            
            self.p_count = 0
            self.q_count=0 
            
            self.label_tree(root)
                        
            constraint = str( self.generate_static_file()  + "\n"
                                    + self.generate_eval(root) +"\n"
                                    + self.generate_constraint() + "\n"
                                    + "(check-synth)")
            # print(constraint)
            soln = self.run_solver(constraint)
            
            if soln:
                predicates_chosen = {}
                for i in range(self.k):
                    for element in soln:
                        if 'p_' + str(i) + '_' in element[0] and element[1] == 'true':
                            predicates_chosen[i] = element[0].replace('p_' + str(i) + '_', '')
                            break
                
                new_root = self.project_copy(root, predicates_chosen)
                    
                return new_root
                
                # return tree, predicates_chosen
                
                
        
        return None


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


def main(): 
    
    t = "true"
    f = "false"
    
    solver2 = SygusDisjunctive(
                        ["cp1", "cp2", "cp3"],
    
                        [[t,t,f,t,t,f],
                        [f,t,f,t,t,f],
                        [f,f,t,t,f,f],
                        [t,f,f,t,f,t]
                        ],
                        
                        k = 3,
                        cdt = ["cp1", "cp2"] 
                        # cdt = [] # (ite  c2 * * )
                     )
    
    print(solver2.make_and(["a"], delim = " "))
    print(solver2.make_and(["a", "b"], delim = " "))
    print(solver2.make_and(["a", "b", "c"], delim = " "))
    print(solver2.make_and(["a", "b", "c", "d", "e"], delim ="\n"))
    
    output_tree = solver2.run_sygus()
    sys.exit(0)

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
            
    strFeatureVectors36 = [
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
            ]

    output = learnHoudiniString(strFeature,strFeatureVectors45)
    solver1  = SygusDisjunctive(
        strFeature,
        strFeatureVectors45,
        k = 1,
        cdt = output
        )
    output_tree = solver1.run_sygus()
    print(output_tree)
    sys.exit(0)
    



main()
