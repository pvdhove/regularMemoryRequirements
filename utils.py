# Copyright (c) 2022 Université de Bordeaux, Université de Mons,
# Université Paris-Saclay
# Use of this source code is governed by an MIT-style
# license that can be found in the LICENSE.md file or at
# https://opensource.org/licenses/MIT.

import math
from automata.fa.dfa import DFA
from automata.fa.nfa import NFA

from IPython.display import Image, display
def view_dfa(dfa):
  plt = Image(dfa.show_diagram().create_png())
  display(plt)

def memory_ready_dfa_from_regex(regex):
  """
  Return a DFA, which has been converted from the regex, and that has been
  transformed to have a single absorbing final state. The language it recognizes
  may not be the same as the regex, but the induced objectives will be the same.
  This automaton can be passed to functions computing memory in file memReq.
  """
  nfa = NFA.from_regex(regex)
  dfa = DFA.from_nfa(nfa)
  
  # Make dfa with a single final absorbing state

  qfin = next(iter(dfa.final_states)) # Extract a random final state
  
  # Redirect all transitions to a final state to qfin
  for q in dfa.states:
    for c in dfa.input_symbols:
      if dfa.transitions[q][c] in dfa.final_states:
        dfa.transitions[q][c] = qfin
  
  # Make final states absorbing
  for q in dfa.final_states:
    for c in dfa.input_symbols:
      dfa.transitions[q][c] = qfin
  
  # Minimize the automata to remove unreachable states and duplicates
  return dfa.minify()

def diamond_generalized(n):
  assert(n >= 1)
  
  states = {str(i) for i in range(3 * n + 1)}
  alphabet = [chr(ord('a') + i) for i in range(2 * n)] # We do not expect n > 13
  transitions = {}
  for state in states:
    transitions[state] = {}
  
  cur_state = 0
  cur_letter = 0
  for _ in range(n):
    transitions[str(cur_state)][alphabet[cur_letter]] = str(cur_state + 1)
    transitions[str(cur_state)][alphabet[cur_letter + 1]] = str(cur_state + 2)
    transitions[str(cur_state + 1)][alphabet[cur_letter + 1]] = str(cur_state + 3)
    transitions[str(cur_state + 2)][alphabet[cur_letter]] = str(cur_state + 3)
    for letter_id in range(len(alphabet)):
      if letter_id != cur_letter and letter_id != cur_letter + 1:
        transitions[str(cur_state)][alphabet[letter_id]] = str(cur_state)
      if letter_id != cur_letter + 1:
        transitions[str(cur_state + 1)][alphabet[letter_id]] = str(cur_state + 1)
      if letter_id != cur_letter:
        transitions[str(cur_state + 2)][alphabet[letter_id]] = str(cur_state + 2)
    cur_state += 3
    cur_letter += 2
  
  # Final accepting state
  for letter in alphabet:
    transitions[str(cur_state)][letter] = str(cur_state)
  
  return DFA(states=states, input_symbols=set(alphabet),
             transitions=transitions, initial_state=str(0),
             final_states={str(3 * n)})

def abab(n):
  assert(n >= 1)
  
  states = {str(i) for i in range(n + 1)}
  alphabet = {'a', 'b'}
  transitions = {}
  for state in states:
    transitions[state] = {}
  
  for i in range(n):
    if i % 2 == 0:
      transitions[str(i)]['a'] = str(i + 1)
      transitions[str(i)]['b'] = str(i)
    else:
      transitions[str(i)]['b'] = str(i + 1)
      transitions[str(i)]['a'] = str(i)
  
  for letter in alphabet:
    transitions[str(n)][letter] = str(n)
  
  return DFA(states=states, input_symbols=alphabet,
             transitions=transitions, initial_state=str(0),
             final_states={str(n)})
  
def aaaa(n):
  assert(n >= 1)
  
  states = {str(i) for i in range(n + 1)}
  alphabet = {'a', 'b'}
  transitions = {}
  for state in states:
    transitions[state] = {}
  
  for i in range(n):
    transitions[str(i)]['a'] = str(i + 1)
    transitions[str(i)]['b'] = str(0)
  
  for letter in alphabet:
    transitions[str(n)][letter] = str(n)
  
  return DFA(states=states, input_symbols=alphabet,
             transitions=transitions, initial_state=str(0),
             final_states={str(n)})

