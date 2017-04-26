/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <util/std_expr.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <map>
#include "memory_model.h"

/*******************************************************************\

Function: memory_model_baset::memory_model_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

memory_model_baset::memory_model_baset(const namespacet &_ns):
  partial_order_concurrencyt(_ns),
  var_cnt(0),
  inv_strategy('\0')
{
}

/*******************************************************************\

Function: memory_model_baset::~memory_model_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

memory_model_baset::~memory_model_baset()
{
}

/*******************************************************************\

Function: memory_model_baset::nondet_bool_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt memory_model_baset::nondet_bool_symbol(
  const std::string &prefix)
{
  return symbol_exprt(
    "memory_model::choice_"+prefix+std::to_string(var_cnt++),
    bool_typet());
}

/*******************************************************************\

Function: memory_model_baset::po

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool memory_model_baset::po(event_it e1, event_it e2)
{
  // within same thread
  if(e1->source.thread_nr==e2->source.thread_nr)
    return numbering[e1]<numbering[e2];
  else
  {
    // in general un-ordered, with exception of thread-spawning
    return false;
  }
}

namespace cpu_refinement {
  //line_number -> (variable_name -> line_number_of_writes+)
  typedef std::map<std::string, std::map<std::string, std::vector<std::string> > > inv_mapt;
  inv_mapt inv_map;
  char inv_strategy = 'l';
  
  void read_invariant_file(const std::string& in, const char &strategy)
  {
    if (strategy == 'a') { inv_strategy = 'a'; return; }
    
    std::ifstream f(in.c_str());
    std::string s;
    while (f.good()) {
      std::string rline, varname;
      uint16_t wc;
      f >> varname >> rline >> wc;
      inv_map[rline][varname].reserve(wc);
      while (wc) {
        std::string wline;
        f >> wline;
        inv_map[rline][varname].push_back(wline);
        wc--;
      }
    }
  }

  //returns true if given read and write pair is present in inv file
  //hack: return true if ignore_write is passed as true and read is present
  bool match_read_write_inv(const irep_idt &rline,
                            const std::string&varname,
                            const irep_idt &wline = irep_idt(),
                            const bool ignore_write = true) {
    
    if (inv_strategy == 'a') { return false; }
    
    std::string srline = id2string(rline);
    if (inv_map.find(srline) != inv_map.end() &&
        inv_map[srline].find(varname) != inv_map[srline].end()) {
      if (ignore_write) {
        return true;
      }
      std::string swline = id2string(wline);
      for (auto wl : inv_map[srline][varname]) {
        if (wl == swline) {
          //read is present as invariant and given write is in defset
          return true;
        }
      }
    }
    return false;
  }
  
}

  
/*******************************************************************\

Function: memory_model_baset::read_from

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::read_from(symex_target_equationt &equation)
{
  cpu_refinement::read_invariant_file(inv_file, inv_strategy);
  
  // We iterate over all the reads, and
  // make them match at least one
  // (internal or external) write.
  
  for(address_mapt::const_iterator
      a_it=address_map.begin();
      a_it!=address_map.end();
      a_it++)
  {
    const a_rect &a_rec=a_it->second;

    for(event_listt::const_iterator
        r_it=a_rec.reads.begin();
        r_it!=a_rec.reads.end();
        r_it++)
    {
      const event_it r=*r_it;

//      std::cout << r->source.pc->source_location << std::endl;
      
      exprt::operandst rf_some_operands;
      exprt::operandst urf_some_operands; //used to maintain underapprox rf

      rf_some_operands.reserve(a_rec.writes.size());
      urf_some_operands.reserve(a_rec.writes.size());

      irep_idt r_src_line = r->source.pc->source_location.get_line();
      std::string r_varname = id2string(r->ssa_lhs.get_object_name());
//      std::cout << "CPU_REFINEMENT: r_varname " << r_varname << std::endl;
      // this is quadratic in #events per address
      for(event_listt::const_iterator
          w_it=a_rec.writes.begin();
          w_it!=a_rec.writes.end();
          ++w_it)
      {
        const event_it w=*w_it;
        // rf cannot contradict program order
        if(po(r, w))
          continue; // contradicts po

        bool track_rf;
        if (w->source.thread_nr == 0) {
          //write from declaration is matched always
          track_rf = cpu_refinement::match_read_write_inv(r_src_line, r_varname);
        } else {
          track_rf = cpu_refinement::match_read_write_inv(r_src_line,
                                                                 r_varname,
                                                                 w->source.pc->source_location.get_line(),
                                                                 false);
        }
        
        bool is_rfi=
          w->source.thread_nr==r->source.thread_nr;

        symbol_exprt s=nondet_bool_symbol("rf");

        // record the symbol
          choice_symbols[
            std::make_pair(r, w)]=s;

        // We rely on the fact that there is at least
        // one write event that has guard 'true'.
        implies_exprt read_from(s,
            and_exprt(w->guard,
              equal_exprt(r->ssa_lhs, w->ssa_lhs)));

        // Uses only the write's guard as precondition, read's guard
        // follows from rf_some
          add_constraint(equation,
                         read_from, is_rfi?"rfi":"rf", r->source);

        if(!is_rfi)
        {
          // if r reads from w, then w must have happened before r
          exprt cond=implies_exprt(s, before(w, r));
            add_constraint(equation,
                           cond, "rf-order", r->source);
        }
        
        if (track_rf && inv_strategy == 'l')
        {
          urf_some_operands.push_back(s);
          // std::cout << r_varname << " " << r_src_line << " "
          //            << w->source.pc->source_location.get_line() << " "
          //            << w->source.thread_nr << std::endl;
        } // else {
        //   std::cout << r_varname << " " << r_src_line << " "
        //             << w->source.pc->source_location.get_line() << " "
        //             << w->source.thread_nr << " " << w->assignment_type << std::endl;
        // }

        rf_some_operands.push_back(s);
      }
      // std::cout << r_varname << " " << r_src_line << " rf size " << rf_some_operands.size()
      //           << " urf size " << urf_some_operands.size() << std::endl;
      // value equals the one of some write
      exprt rf_some;
      uint64_t write_diff = rf_some_operands.size() - urf_some_operands.size();
//      std::cout << r_varname << " " << write_diff << std::endl;
      if (rf_some_operands.empty()) {
        // uninitialised global symbol like symex_dynamic::dynamic_object*
        // or *$object
        continue;
      } else {
        if (rf_some_operands.size() == 1) {
          rf_some = rf_some_operands.front();
        } else {
          if (inv_strategy == 'a') {
            urf_some_operands.clear();
            for (unsigned int i = 0; i < rf_some_operands.size()/2; i++) {
              urf_some_operands.push_back(rf_some_operands[i]);
            }
          }
          rf_some = or_exprt();
          rf_some.operands().swap(rf_some_operands);
        }
      }

      exprt urf_some;
      if (urf_some_operands.empty() || write_diff == 0) {
      // Add the read's guard, each of the writes' guards is implied
      // by each entry in rf_some
//        std::cout << "default encoding: " << r_src_line << std::endl;
          add_constraint(equation,
                         implies_exprt(r->guard, rf_some), "rf-some", r->source);
      } else {
        if (urf_some_operands.size() == 1) {
          urf_some = urf_some_operands.front();
        } else {
          urf_some = or_exprt();
          urf_some.operands().swap(urf_some_operands);
        }        
        //we will add following constraint:
        //is_local -> internal writes && !is_local -> original set of writes
        //<=> (!is_local || some internal write) && (is_local || some original set of writes)
//        std::cout << "new encoding: " << r_src_line << std::endl;
        symbol_exprt is_local = nondet_bool_symbol("is_local");
        #ifdef COUNT_WRITE_SAVING
        write_save_map[is_local.get_identifier()] = write_diff;
        #endif
//        std::cout << "Added: " << r_varname << " " << r_src_line << " " << write_diff << std::endl;
//        write_saving_map[is_local.get_identifier()] = write_diff;
        // exprt combined_constraint = and_exprt(or_exprt(not_exprt(is_local), urf_some),
        //                                       or_exprt(is_local, rf_some));
        and_exprt combined_constraint = and_exprt(implies_exprt(is_local, urf_some),
                                                  implies_exprt(not_exprt(is_local),rf_some));
        
        //      exprt combined_constraint = or_exprt(not_exprt(is_local), urf_some);
//        std::cout << from_expr(ns, "", combined_constraint) << std::endl;

        // std::cout << from_expr(ns, "", urf_some) << std::endl;
        // add_constraint(equation,
        //                implies_exprt(r->guard, combined_constraint), "rf-some", r->source);
        add_constraint(equation,
                       implies_exprt(r->guard, combined_constraint), "rf-some", r->source);

      }
        
      // uninitialised global symbol like symex_dynamic::dynamic_object*
      // or *$object
      // if(rf_some_operands.empty())
      //   continue;
      // else if(rf_some_operands.size()==1)
      //   rf_some=rf_some_operands.front();
      // else
      // {
      //   rf_some=or_exprt();
      //   rf_some.operands().swap(rf_some_operands);
      // }

      // Add the read's guard, each of the writes' guards is implied
      // by each entry in rf_some
      // add_constraint(equation,
      //   implies_exprt(r->guard, rf_some), "rf-some", r->source);
    }
  }
}
