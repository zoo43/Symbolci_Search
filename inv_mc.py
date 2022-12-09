import pynusmv
from pynusmv.fsm import BddTrans
import sys



def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def reachable(fsm, spec):
    """
    Returns the set of reachable states in the FSM
    """
    reach = fsm.init
    new = list ()
    new.append(fsm.init)
    checkInvar = True, fsm.init
    found = False
    counter = 0
    iteration = 0
    while new[counter].size != 1:
        spec_bbd = spec_to_bdd(fsm, spec)
        if(new[counter].intersected(spec_bbd.not_()) and found == False):
            checkInvar = False, fsm.pick_one_state(new[counter].intersection(spec_bbd.not_()))
            #lock so 
            found = True
            iteration = counter
        new.append(fsm.post(new[counter], None).diff(reach))
        reach = reach.union(new[counter])
        counter = counter + 1
    
    iterationCounter = iteration
    state = checkInvar[1]
    #get all the closest initial states from our counterexample state
    while(iterationCounter > 0):
        state = fsm.pre(state).intersection(reach)
        iterationCounter = iterationCounter - 1
    state = state.intersection(fsm.init)
    #get all the set of states between the initials and our counterexample
    postImages = list ()
    while(iterationCounter < iteration):
        postImages.append(state)
        state = fsm.post(state)
        iterationCounter = iterationCounter + 1
    return checkInvar, reach, postImages, iteration

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
    invResp, reachableStatesBDD, images, intersection = reachable(fsm, spec)
    invarResp, counterExample = invResp
    state = counterExample
    trace = ""
    trace = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__()
    counter = intersection
    while (state.intersected(fsm.init) == False):
        getPreState = fsm.pick_one_state(fsm.pre(state).intersection(images[counter - 1]))
        state_to_add = pynusmv.dd.State.from_bdd(getPreState, fsm).get_str_values().__str__() + ", "
        input_to_add = pynusmv.dd.Inputs.from_bdd(fsm.get_inputs_between_states(getPreState, state), fsm).get_str_values().__str__() + ", "
        trace = state_to_add + input_to_add + trace
        state = getPreState
        counter = counter - 1

    return invarResp, trace



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
