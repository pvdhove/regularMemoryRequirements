# Copyright (c) 2022 Université de Bordeaux, Université de Mons,
# Université Paris-Saclay
# Use of this source code is governed by an MIT-style
# license that can be found in the LICENSE.md file or at
# https://opensource.org/licenses/MIT.

from automata.fa.dfa import DFA # python3 -m pip install automata-lib
from pysat.formula import IDPool, CNF # python3 -m pip install python-sat
from pysat.solvers import Solver
from itertools import product

# Possible improvement: PySat only uses a single thread, but using SAT solvers
# directly may use more threads.

def single_final_absorbing_state(aut):
  """
  Return the only accepting state of aut, which must be absorbing. If aut is not
  absorbing or aut has none or multiple accepting states, raise ValueError.
  """
  if len(aut.final_states) != 1:
    raise ValueError("The automaton must have exactly one final state")
  
  qfin = next(iter(aut.final_states)) # Extract the only final state
  
  for c in aut.input_symbols:
    if aut.transitions[qfin][c] != qfin:
      raise ValueError("The only final state of the automaton must be absorbing")
  
  return qfin

def compute_comparable(aut):
  """
  Return two lists smaller_than and greater_than mapping to each state i of aut
  a set smaller_than[i] (resp. greater_than[i]) containing all the states
  smaller than (resp. greater than) state i for the prefix preorder.
  """
  # List of sets: for each state, store the ones that are known to be smaller
  # or greater.
  smaller_than = {}
  greater_than = {}
  for state in aut.states:
    smaller_than[state] = set()
    greater_than[state] = set()
  state_list = list(aut.states)
  n = len(state_list)
  
  # Makes two copies of aut
  aut1, aut2 = aut.copy(), aut.copy()
  # For all pairs of states
  for q1_id in range(n):
    for q2_id in range(q1_id + 1, n):
      q1, q2 = state_list[q1_id], state_list[q2_id]
      # If not yet known to be comparable
      if q1 not in smaller_than[q2] and q1 not in greater_than[q2]:
        aut1.initial_state = q1
        aut2.initial_state = q2
        
        # If q1 <= q2
        if aut1.issubset(aut2):
          greater_than[q1].add(q2)
          smaller_than[q2].add(q1)
          # Deduce what is possible from what was already known
          for q3 in greater_than[q2]:
            greater_than[q1].add(q3)
            smaller_than[q3].add(q1)
          for q3 in smaller_than[q1]:
            greater_than[q3].add(q2)
            smaller_than[q2].add(q3)
        
        # If q2 <= q1
        if aut2.issubset(aut1):
          greater_than[q2].add(q1)
          smaller_than[q1].add(q2)
          # Deduce what is possible from what was already known
          for q3 in greater_than[q1]:
            greater_than[q2].add(q3)
            smaller_than[q3].add(q2)
          for q3 in smaller_than[q2]:
            greater_than[q3].add(q1)
            smaller_than[q1].add(q3)

  return smaller_than, greater_than

# The following functions are used to assign integers to variables in the SAT
# encoding, using the IDPool mechanism from pysat. 

# x_{q, i} is true if state q is in the i^th chain
def _x_qi_to_id(vpool):
  return lambda q, i: vpool.id('x_{0}_{1}'.format(q, i))

# Represents AND_q (x_{q, i} -> x_{d(q, c), j})
def _y_cij_to_id(vpool):
  return lambda c, i, j: vpool.id('y_{0}_{1}_{2}'.format(c, i, j))

# Represents (x_{q, i} -> x_{d(q, c), j})
def _z_cijq_to_id(vpool):
  return lambda c, i, j, q: vpool.id('z_{0}_{1}_{2}_{3}'.format(c, i, j, q))

# Encodes the following constraint in CNF:
# each set is a chain -- two states non comparable cannot be in the same set.
def _each_set_is_a_chain(cnf, k, states, comparable_to, x_qi):
  state_list = list(states)
  n = len(state_list)
  for q1_id in range(n):
    q1 = state_list[q1_id]
    for q2_id in range(q1_id + 1, n):
      q2 = state_list[q2_id]
      if q2 not in comparable_to[q1]:
        for i in range(k):
          cnf.append([-x_qi(q1, i), -x_qi(q2, i)])

# Encodes the following constraint in CNF:
# each chain maps into some chain when a letter is read. This formula is
# more complicated as it requires a conversion from the formula
#              AND_c AND_i OR_j AND_q (x_{q, i} -> x_{d(q, c), j})
# into CNF. To transform it, we use a Tseytin transformation (increases the
# number of clauses and variables linearly). Here, we add variables y_cij
# and z_cijq.
def _sets_stable_by_reading_colors(cnf, k, states, alphabet, delta, x_qi, y_cij, z_cijq):
  # These first loops represent AND_c AND_i OR_j y_cij.
  # We require afterwards that y_cij <=> AND_q (x_{q, i} -> x_{d(q, c), j}.
  for c in alphabet:
    for i in range(k):
      cnf.append([y_cij(c, i, j) for j in range(k)])
  
  # We now need that (y_cij <=> AND_q (x_{q, i} -> x_{d(q, c), j})).
  # We use that z_cijq <=> (x_{q, i} -> x_{d(q, c), j}) (encoded later).
  for c in alphabet:
    for i in range(k):
      for j in range(k):
        ycij = y_cij(c, i, j)
        cnf.append([ycij] + [z_cijq(c, i, j, q) for q in states])
        for q in states:
          cnf.append([-ycij, -x_qi(q, i), x_qi(delta[q][c], j)])
          
  # We now need that z_cijq <=> (x_{q, i} -> x_{d(q, c), j)})
  #                         <=> (-x_{q, i} OR x_{d(q, c), j}).
  for q in states:
    for i in range(k):
      xqi = x_qi(q, i)
      for c in alphabet:
        for j in range(k):
          zcijq = z_cijq(c, i, j, q)
          xdqcj = x_qi(delta[q][c], j)
          cnf.append([zcijq, xqi])
          cnf.append([zcijq, -xdqcj])
          cnf.append([-zcijq, -xqi, xdqcj])

def monotone(aut, solver="m22"):
  """
  Return true if there exists a monotone decomposition of automaton aut in k
  sets. Calling monotone(aut) precomputes a few things and returns a function
  taking an integer parameter k as an input. The SAT solver for pysat can be
  chosen (m22 by default).
  
  Automaton aut should be a DFA with a single absorbing final state.
  """

  final = single_final_absorbing_state(aut)
  
  states = aut.states
  alphabet = aut.input_symbols
  delta = aut.transitions
  smaller_than, greater_than = compute_comparable(aut)
  # Merges the states smaller than and the states greater than
  comparable_to = {}
  for q in states:
    comparable_to[q] = smaller_than[q].union(greater_than[q])

  vpool = IDPool(start_from=1) # Used to remember an integer for each variable
  x_qi = _x_qi_to_id(vpool)
  y_cij = _y_cij_to_id(vpool)
  z_cijq = _z_cijq_to_id(vpool)
  
  def f(k):
    cnf = CNF()
    
    # Each state is in a set
    for q in states:
      cnf.append([x_qi(q, i) for i in range(k)])
    
    # Each set is a chain -- two states non comparable cannot be in the same set
    _each_set_is_a_chain(cnf, k, states, comparable_to, x_qi)
    
    # Each chain maps into some chain when a letter is read
    _sets_stable_by_reading_colors(cnf, k, states, alphabet, delta,\
                                   x_qi, y_cij, z_cijq)
    
    s = Solver(name=solver, bootstrap_with=cnf)
    print("SAT encoding finished with " + str(k) + " states, solving...", flush=True)
    # We can assume that the final absorbing state is in all chains
    return s.solve(assumptions=[x_qi(final, i) for i in range(k)]),\
           s.get_model(),\
           x_qi
  return f

def monotone_valuation_to_aut(aut, k, val, state_in_chain, verbose=True):
  """
  If monotone(aut, k) returns (True, val, state_in_chain), the call
  monotone_valuation_to_aut(aut, k, val, state_in_chain) returns a memory
  structure M with k states such that L(aut) is M-strongly-monotone.
  This only uses the variable assignment obtained from the SAT solver in the
  monotone(aut, k) call.
  
  If verbose is True (which is the default value), displays a monotone
  decomposition corresponding to the memory structure.
  """
  states = {str(i) for i in range(k)}
  alphabet = aut.input_symbols
  transitions = {}
  for state in states:
    transitions[state] = {}
  is_state_in_chain = lambda q, i : val[state_in_chain(q, i) - 1] > 0
  
  # Determine initial state
  for i in range(k):
    if is_state_in_chain(aut.initial_state, i):
      initial_state = str(i)
      break
  
  # Can be used to display the \Gamma(m) sets for debug
  if verbose:
    smaller_than, _ = compute_comparable(aut)
    for i in range(k):
      chain_i = []
      for q in aut.states:
        if is_state_in_chain(q, i):
          chain_i.append(q)
      # Display states in order given by the prefix preorder
      chain_i.sort(key = lambda q : len(smaller_than[q]))
      print("\\Gamma_" + str(i) + " = " + str(chain_i))
  
  # Create transitions
  for i in range(k):
    for c in alphabet:
      for j in range(k):
        ic_j = True # Is delta(\Gamma_i, c) \subseteq \Gamma_j?
        for q in aut.states:
          if is_state_in_chain(q, i) and not is_state_in_chain(aut.transitions[q][c], j):
            ic_j = False
            break
        if ic_j:
          transitions[str(i)][c] = str(j)
          break
  
  return DFA(states=states, input_symbols=alphabet, transitions=transitions,
             initial_state=initial_state, final_states=set())

def smallest_memory_safety(aut, verbose=True):
  """
  Return a smallest memory structure for the regular safety objective derived
  from aut (i.e., Safe(L(aut))). Equivalently, return a structure M with
  minimally many states such that automaton aut is M-strongly-monotone.
  This performs a binary search on the number of states, relying on the
  monotone() function and then on the monotone_valuation_to_aut() function.
  Automaton aut should be a DFA with a single absorbing final state.
  """
  n = len(aut.states)
  l = 0 # Never possible with 0 states in M
  r = n - 1 # Always possible with n - 1 states in M (all except final state)
  f = monotone(aut, solver="m22")
  
  best_val = None
  best_state_in_chain = None
  
  while l < r - 1:
    mid = (l + r + 1) // 2
    if verbose:
      print("Trying with " + str(mid) + " states...", flush=True)
    b, val, state_in_chain = f(mid)
    if verbose:
      print("Solved!", end="")
      print((" P" if b else " Not p") + "ossible with " + str(mid) + " states.",
          flush=True)
    if b:
      best_val = val
      best_state_in_chain = state_in_chain
      r = mid
    else:
      l = mid
  
  if best_val is None:
    _, best_val, best_state_in_chain = f(r)
  return monotone_valuation_to_aut(aut, r, best_val, best_state_in_chain, verbose)

# ------------------------------------------------------------
# MEMORY FOR REGULAR REACHABILITY OBJECTIVES

# d_{m, c, m'} is true if there is a transition from m to m' with color c
def _d_mcm_to_id(vpool):
  return lambda m1, c, m2: vpool.id('d_{0}_{1}_{2}'.format(m1, c, m2))

# p_{m, m', q1, q1', q2, q2'} is true if (m, q1, q2) is reachable in the product
# M x Q x Q, and there is a path from (m, q1, q2) to (m', q1', q2').
def _p_mmqqqq_to_id(vpool):
  return lambda m1, m2, q1, q2, p1, p2:\
         vpool.id('p_{0}_{1}_{2}_{3}_{4}_{5}'.format(m1, m2, q1, q2, p1, p2))

def progress_consistent(aut, monotone=False, solver="m22"):
  """
  A call to progress_consistent(aut)(k) returns true if there exists a memory
  structure M with k states such that the regular reachability objective derived
  from aut is M-progress-consistent. Calling progress_consistent(aut)
  precomputes a few things and returns a function taking the integer parameter k
  as an input. The SAT solver for pysat can be chosen (m22 by default).
  If parameter monotone is True, then also requires that the objective is
  M-strongly-monotone.
  
  Automaton aut should be a DFA with a single final absorbing state.
  """
  final = single_final_absorbing_state(aut)
  
  init = aut.initial_state
  states = aut.states
  delta = aut.transitions
  alphabet = aut.input_symbols
  smaller_than, greater_than = compute_comparable(aut)

  vpool = IDPool(start_from=1)
  d_mcm = _d_mcm_to_id(vpool)
  p_mqp = _p_mmqqqq_to_id(vpool)
  
  def f(k):
    cnf = CNF()
    
    # Structure M is complete
    for m1 in range(k):
      for c in alphabet:
        cnf.append([d_mcm(m1, c, m2) for m2 in range(k)])
    
    # Initial state is reachable, fixed at 0 for M
    cnf.append([p_mqp(0, 0, init, init, init, init)])
    
    # Reachable states of the product
    for q in states:
      for c in alphabet:
        qc = delta[q][c]
        for m1 in range(k):
          for m2 in range(k):
            # (p_mqp(m1, m1, q, q, q, q) AND d_mcm(m1, c, m2))
            # -> p_mqp(m2, m2, qc, qc, qc, qc)
            cnf.append([-p_mqp(m1, m1, q, q, q, q), -d_mcm(m1, c, m2),
                         p_mqp(m2, m2, qc, qc, qc, qc)])
    
    # Consider states in product M x Q x Q not necessarily reachable
    for m in range(k):
      for q1, q2 in product(states, repeat=2):
        cnf.append([-p_mqp(m, m, q1, q1, q1, q1), -p_mqp(m, m, q2, q2, q2, q2),
                     p_mqp(m, m, q1, q1, q2, q2)])
    
    # Augment paths
    for q2, p2 in product(states, repeat=2):
      for c in alphabet:
        q2c, p2c = delta[q2][c], delta[p2][c]
        for m1, m2, m3 in product(range(k), repeat=3): # product from itertools
          for q1, p1 in product(states, repeat=2):
            cnf.append([-p_mqp(m1, m2, q1, q2, p1, p2), -d_mcm(m2, c, m3),
                         p_mqp(m1, m3, q1, q2c, p1, p2c)])
    
    # Implement the NP reformulation of M-progress-consistency
    for m in range(k):
      for q1 in states:
        for q2 in greater_than[q1]:
          if q2 != final:
            cnf.append([-p_mqp(0, m, init, q1, init, q1),
                        -p_mqp(m, m, q1, q2, q2, q2)])
    
    if monotone:
      # Is state (q, m) reachable in the product?
      x_qi = lambda q, m: p_mqp(m, m, q, q, q, q)
      y_cij = _y_cij_to_id(vpool)
      z_cijq = _z_cijq_to_id(vpool)
      comparable_to = {}
      for q in states:
        comparable_to[q] = smaller_than[q].union(greater_than[q])
      
      # We encode the three properties for M-monotony as in monotone().
      # Note that as M is complete, every reachable state q of aut has an m
      # such that (q, m) is reachable in the product.
      # So, we skip the first property.
      
      # Each set is a chain: two non comparable states cannot be in the same set
      _each_set_is_a_chain(cnf, k, states, comparable_to, x_qi)
    
      # Each chain maps into some chain when a letter is read
      _sets_stable_by_reading_colors(cnf, k, states, alphabet, delta,\
                                     x_qi, y_cij, z_cijq)
    
    s = Solver(name=solver, bootstrap_with=cnf)
    print("SAT encoding finished with " + str(k) + " states, solving...", flush=True)
    b, val = s.solve(assumptions=[]), s.get_model()
    return b, val, d_mcm
  return f

def progress_consistent_valuation_to_aut(aut, k, val, d_mcm):
  """
  If progress_consistent(aut)(k) returns (True, val, d_mcm), the call
  progress_consistent_valuation_to_aut(aut, k, val, state_in_chain) returns a
  memory structure M with k states such that L(aut) is M-progress-consistent.
  This only uses the variable assignment obtained from the SAT solver in the
  progress-consistent(aut)(k) function.
  """
  states = {str(i) for i in range(k)}
  alphabet = aut.input_symbols
  transitions = {}
  for state in states:
    transitions[state] = {}
  initial_state = str(0)
  is_mcm = lambda m1, c, m2 : val[d_mcm(m1, c, m2) - 1] > 0
  
  # Create transitions
  for m1 in range(k):
    for c in alphabet:
      for m2 in range(k):
        if is_mcm(m1, c, m2):
          transitions[str(m1)][c] = str(m2)
          break # Removing this break allows for non-deterministic M, where all
                # sub-deterministic memory structures are acceptable
  
  return DFA(states=states, input_symbols=alphabet, transitions=transitions,
             initial_state=initial_state, final_states=set())

def smallest_memory_reachability(aut, monotone=True, verbose=True):
  """
  Return a smallest memory structure M that suffices to play optimally for the
  regular reachability objective derived from aut (i.e., Reach(L(aut))).
  Equivalently, return a structure M with minimally many states such that
  automaton aut is M-progress-consistent and M-strongly-monotone. This performs
  a binary search on the number of states, relying on the progress_consistent()
  function and then on the progress_consistent_valuation_to_aut() function.
  If monotone is False, then drops the M-strong-monotony requirement (which
  means that the structure M may not suffice to play optimally, but will be the
  smallest M such that the objective is M-progress-consistent).
  Automaton aut should be a DFA with a single absorbing final state.
  """
  n = len(aut.states)
  l = 0 # Never possible with 0 states in M
  r = n - 1 # Always possible with n - 1 states in M (all except final state)
  f = progress_consistent(aut, monotone=monotone, solver="m22")
  
  best_val = None
  best_d_mcm = None
  
  while l < r - 1:
    mid = (l + r + 1) // 2
    if verbose:
      print("Trying with " + str(mid) + " states...", flush=True)
    b, val, d_mcm = f(mid)
    if verbose:
      print("Solved!", end="")
      print((" P" if b else " Not p") + "ossible with " + str(mid) + " states.",
          flush=True)
    if b:
      best_val = val
      best_d_mcm = d_mcm
      r = mid
    else:
      l = mid
  
  if best_val is None:
    _, best_val, best_d_mcm = f(r)
  return progress_consistent_valuation_to_aut(aut, r, best_val, best_d_mcm)

