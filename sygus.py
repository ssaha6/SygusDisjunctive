from  command_runner import runCommand
import re

distcintConditionals = True

class Nd:
    def __init__(self):
        self.data = None
        self.left = None
        self.right = None
    
    def __str__(self):
        if not self.left and not self.right:
            return "*"
            # if len(self.data) == 1:
            #     return self.data[0]
            # else: 
            #     return "(and " + ' '.join(self.data) + ")" 
            
        else:
            return " ".join(["(ite ", str(self.data),str(self.right),  str(self.left), ")"])
    
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
        for k_itr in range(self.k):
            self.pvariables[k_itr] = []
            for p_itr in self.cond_pred:
                self.pvariables[k_itr].append('p_'+str(k_itr) + '_' + p_itr)
        
        self.wvariables = [] 
        self.uvariables = []
        for pred  in self.cond_pred: 
            self.wvariables.append('w_'+pred)
            self.uvariables.append('u_'+pred)
        
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
        return "( set-logic " + logic + " )\n"
    
    def synth_conditionals(self):
        ret = ''
        for k, value in self.pvariables.items():
            ret += '\n'.join(self.zip_column('(synth-fun ', value, '() Bool )' )) + '\n'
        return ret
    
    def synth_witness(self):
        return '\n'.join(self.zip_column( '(synth-fun ', self.wvariables, ' () Bool)' ))
    
    def declare_universal_variables(self):
        return '\n'.join(self.zip_column( '(declare-var ', self.uvariables,  ' Bool)'))
    
    def define_CDT(self):
        ret = "(define-fun cdt (" 
        ret +=  ' '.join([ "( " + x + " Bool)" for x in self.cond_pred])
        ret += ") Bool \n " + self.cdt + "\n)\n"  
        return ret
    
    def generate_constraint(self):
        ret = "(constraint \n(and\n"
                
        for k_itr in range(self.k):
            ret += "(or " + ' '.join(self.pvariables[k_itr]) + ")\n"
            for p_itr in range(len(self.pvariables[k_itr])):
                    ret += "(=> " + self.pvariables[k_itr][p_itr] + " (and "
                    ret += ' '.join(list(map(lambda x: "( not " + x + ")", self.pvariables[k_itr][0:p_itr] + self.pvariables[k_itr][p_itr+1:]))) 
                    ret += "))\n"
            
        ret += '( => ( eval ' + ' '.join(self.uvariables) + ' ' \
                              + ") (cdt " + ' '.join(self.uvariables) + "))\n"
                              
        ret += "(cdt " + ' '.join(self.wvariables) + ")\n"
        ret += "(not (eval " + " ".join(self.wvariables) + " ))\n"
        
        
        if distcintConditionals:
            # add constraint if a predicate is chosen no other node can have that predicate
            # p_i_c => and (not p_j_c) 
            if self.k > 1:
                for p_itr in range(len(self.cond_pred)):
                    for i in range(self.k):
                        ret += "(=>  p_" + str(i) + "_" + self.cond_pred[p_itr] + " (and true "
                        for j in range(self.k):
                            if i == j:
                                continue
                            ret += " (not p_" + str(j) + "_" + self.cond_pred[p_itr] + " )" 
                        ret += ") )\n"
        
        
        ret += "))"
        return ret
    
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
            root.selectme = [ "" for i in range(len(self.cond_pred_data))] 
        
        if not root.left and not root.right:
            root.k = self.q_count
            self.q_count += 1
            
            ret = "(and \n"
            for cond_itr in range(len(self.cond_pred)):
                ret += "(=> (not " + self.cond_pred[cond_itr] + " )\n(or\n"
                ret += '\n'.join(self.zip_column('(and', root.selectme, 
                                    '(not ' ,  [ x[cond_itr] for x in self.cond_pred_data],  '))' ))
                ret += "\n)\n)\n"
            ret += ")\n"
            
            root.constraint = ret
        
        
        
        else:
            root.k = self.p_count
            self.p_count += 1
            
            current_selectme = self.selectme_statement(root.k)
            
            root.left.selectme = self.zip_column(root.selectme, "(not ", current_selectme, ")")
            root.right.selectme = self.zip_column(root.selectme, current_selectme)
            
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
        ret= str("(define-fun eval (" + ' '.join(["( " + x + " Bool)" for x in self.cond_pred]) 
                                   + ") Bool\n")
        
        ret += self.tree_to_smt(root) + "\n)\n"
        return ret
    
    
    def run_solver(self, constraint):
        
        with open("sygus.sl", "w") as file:
            file.write(constraint)
        
        output = runCommand(["./cvc4-2020-02-06-win64-opt.exe", "--sygus-out=sygus-standard",  "--lang=sygus2", "sygus.sl"])
        
        if output: 
            if "\r\nb" in output: 
                output = re.sub("\'?\\r\\nb\'?", "\n", output)

            valuation = re.findall('\s*\(define\-fun\s+(.*)\s+\(\s*\)\s+Bool\s+(.*)\s*\)', output) 
            if len(valuation) == 0:
                return None
            else:
                return valuation 
            
        return None
    
    
    def project_copy(self, root, predicates_chosen):
        if not root:
            return None
        
        new_root = Nd()
        
        if not root.left and not root.right:
            new_root.data = "*"
            # new_root.data = equalities_chosen[root.k]
            
            
        else:
            new_root.data = predicates_chosen[root.k]
            new_root.left = self.project_copy(root.left, predicates_chosen)
            new_root.right = self.project_copy(root.right, predicates_chosen)
        
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
