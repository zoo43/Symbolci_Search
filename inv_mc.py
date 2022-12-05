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
    while (state.intersected(fsm.init) == False):
        state = fsm.pre(state)
        print(pynusmv.dd.State.from_bdd(state, fsm).get_str_values())
    return string

def get_all_post(fsm, state):
    string = ""
    while (state.intersected(fsm.init) == False):
        string = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__() + ", {}, " + string 
        #print(pynusmv.dd.State.from_bdd(state, fsm).get_str_values())
        state = fsm.trans.post(state)
    #string = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__() + ", {}, " + string 
    return string

def reachable(fsm, spec):
    """
    Returns the set of reachable states in the FSM
    """
    reach = fsm.init
    new = fsm.init
    #st = ""
    checkInvar = True, new#, st
    found = False
    while new.size != 1:
        #st = st + pynusmv.dd.State.from_bdd(new, fsm).get_str_values().__str__() + ", " + pynusmv.dd.Inputs.from_bdd(new,fsm).get_str_values().__str__() + ", "
        #If the intersection of states that I can reach is not empty. Then those states are not reachable and I have to use them to check things
        spec_bbd = spec_to_bdd(fsm, spec)
        if(new.intersected(spec_bbd.not_()) and found == False):
            checkInvar = False, new.intersection(spec_bbd.not_())#, st
            found = True
        new = fsm.post(new, None).diff(reach)
        reach = reach.union(new)
    return checkInvar, reach

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
    fsm = pynusmv.glob.prop_database().master.bddFsm
    fsm.pick_all_inputs
    invResp, reachableStatesBDD = reachable(fsm, spec)
    invarResp, counterExample = invResp
    state = counterExample
    trace = ""
    trace = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__()
    while (state.intersected(fsm.init) == False):
        getPreState = fsm.pre(state).intersection(reachableStatesBDD)
        trace = pynusmv.dd.State.from_bdd(getPreState, fsm).get_str_values().__str__() + ", " + pynusmv.dd.Inputs.from_bdd(fsm.get_inputs_between_states(getPreState, state), fsm).get_str_values().__str__() + ", " + trace
        #trace = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__() + "---->" + (','.join([str(i.get_str_values().__str__()) for i in fsm.pick_all_states(fsm.pre(state))])) + "\n"
        state = fsm.pre(state).intersection(fsm.reachable_states)
        print(trace)
    trace = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__() + ", " + trace
    #print(pynusmv.dd.State.from_bdd(fsm.pre(reachableStatesBDD), fsm).get_str_values().__str__() + pynusmv.dd.Inputs.from_bdd(fsm.get_inputs_between_states(fsm.pre(reachableStatesBDD), reachableStatesBDD), fsm).get_str_values().__str__())
    #if(reachableStatesBDD.intersected(spec_to_bdd(fsm, spec).not_())):
    #    intersection = reachableStatesBDD.intersection(spec_to_bdd(fsm, spec).not_())
        #print(pynusmv.dd.Inputs.from_bdd(intersection, fsm).get_str_values())
    return invarResp, trace#get_all_pre(fsm, reachableStatesBDD)
    #return True, None




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
