import pynusmv
from pynusmv.fsm import BddTrans
import sys



def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def get_all_pre(fsm, state):
    string = ""
    while (state != fsm.init):
        string = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__() + ", " + string 
        #print(pynusmv.dd.State.from_bdd(state, fsm).get_str_values())
        state = fsm.trans.pre(state)
    string = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__() + ", " + string 
    return string

def check_explain_inv_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ennding with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """

    #ltlspec = pynusmv.prop.g(spec)
    fsm = pynusmv.glob.prop_database().master.bddFsm
    
    reach = fsm.init
    new = fsm.init
    #get_all_pre(fsm, fsm.trans.post(fsm.trans.post(new)))
    #for state in fsm.pick_all_states(fsm.trans.pre(fsm.trans.post(fsm.trans.post(new)))):
    #    print(state.get_str_values())

    #new = fsm.trans.post(new)
    #print (pynusmv.dd.StateInputs(new, fsm))
    while new.size != 1:
        if new.intersected(spec_to_bdd(fsm, spec)) == False:
            return False, get_all_pre(fsm, new)
        else:
            new = fsm.trans.post(new).diff(reach)
            reach = reach.union(new)
    return True, None      
    """
    while new.size != 1:
        if new.intersected(spec_to_bdd(fsm,spec)):
            return True, None

        new = fsm.trans.post(new).diff(reach)
        #print(new) pick all states
        reach = reach.union(new)

    return False,"paolo"
    



    res, trace = True,None
    #res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)
    return res, trace
    """
if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
        res, trace = check_explain_inv_spec(spec)
        if res == True:
            print("Invariant is respected")
        else:
            print("Invariant is not respected")
            print(trace)
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()
