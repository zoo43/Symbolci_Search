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
    Returns the set of reachable states in the FSM and if a counterexample is found
    """
    #initialize needed variables
    reach = fsm.init
    new = fsm.init
    checkInvar = True, fsm.init
    found = False
    counter = 0
    iteration = 0
    #while new is not empty
    while new.size != 1:
        spec_bbd = spec_to_bdd(fsm, spec)
        #check if there's a counterexample in our current set of states
        if(new.intersected(spec_bbd.not_()) and not found):
            checkInvar = False, fsm.pick_one_state(new.intersection(spec_bbd.not_()))
            #lock so we keep the closest counterexample to the initial states
            found = True
            iteration = counter
        #get the next set of states
        new = fsm.post(new).diff(reach)
        #update the reachable states
        reach = reach.union(new)

        counter = counter + 1

    return checkInvar, reach, iteration

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
    #get invariant response, set of reachable states and 
    #number of iterations to reach the counterexample (from closest initial states)
    invResp, reachableStatesBDD, iteration = reachable(fsm, spec)
    counterFound, counterExample = invResp
    iterationCounter = iteration
    state = counterExample

    #get all the closest initial states from our counterexample state
    while(iterationCounter > 0):
        state = fsm.pre(state).intersection(reachableStatesBDD)
        iterationCounter = iterationCounter - 1
    #remove the traces to other initial states
    state = state.intersection(fsm.init)
    #get all the set of states between the closest initials 
    #and our counterexample(removing the traces to the furthest initial states)
    postImages = list ()
    while(iterationCounter < iteration):
        postImages.append(state)
        state = fsm.post(state)
        iterationCounter = iterationCounter + 1

    state = counterExample
    #print the counter example state
    trace = pynusmv.dd.State.from_bdd(state, fsm).get_str_values().__str__()
    counter = iteration
    while (not state.intersected(fsm.init) and counter >= 0):
        #pick one state ensuring we keep only trace to the closest ones
        preState = fsm.pick_one_state(fsm.pre(state).intersection(postImages[counter - 1]))
        #prepare the data to add to print
        state_to_add = pynusmv.dd.State.from_bdd(preState, fsm).get_str_values().__str__() + ", "
        input_to_add = pynusmv.dd.Inputs.from_bdd(fsm.get_inputs_between_states(preState, state), fsm).get_str_values().__str__() + ", "
        trace = state_to_add + input_to_add + trace
        #update our current state
        state = preState
        counter = counter - 1

    return counterFound, trace



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
