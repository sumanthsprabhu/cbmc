/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_MEMORY_MODEL_H
#define CPROVER_GOTO_SYMEX_MEMORY_MODEL_H

#include "partial_order_concurrency.h"

class memory_model_baset:public partial_order_concurrencyt
{
public:
  explicit memory_model_baset(const namespacet &_ns);
  virtual ~memory_model_baset();

  virtual void operator()(symex_target_equationt &)=0;

  void set_invariant_file(const std::string &in) { inv_file = in; }
  void set_invariant_strategy(const char &s) { inv_strategy = s; }
#ifdef COUNT_WRITE_SAVING
    std::map<irep_idt, uint64_t> write_save_map;
    std::map<irep_idt, uint64_t> total_writes_map;
#endif
protected:
  // program order
  bool po(event_it e1, event_it e2);

  // produce fresh symbols
  unsigned var_cnt;
  symbol_exprt nondet_bool_symbol(const std::string &prefix);

  // This gives us the choice symbol for an R-W pair;
  // built by the method below.
  typedef std::map<
    std::pair<event_it, event_it>, symbol_exprt> choice_symbolst;
  choice_symbolst choice_symbols;

  void read_from(symex_target_equationt &equation);

  // maps thread numbers to an event list
  typedef std::map<unsigned, event_listt> per_thread_mapt;

  std::string inv_file;
  char inv_strategy;
};

#endif // CPROVER_GOTO_SYMEX_MEMORY_MODEL_H
