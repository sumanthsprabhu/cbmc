/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <solvers/sat/dimacs_cnf.h>
#include <util/time_stopping.h>

#include <util/xml.h>

#include "bv_refinement.h"

/*******************************************************************\

Function: bv_refinementt::bv_refinementt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_refinementt::bv_refinementt(
  const namespacet &_ns, propt &_prop):
  bv_pointerst(_ns, _prop),
  max_node_refinement(5),
  do_array_refinement(true),
  do_arithmetic_refinement(true),
  do_cpu_refinement(false)
{
  // check features we need
  assert(prop.has_set_assumptions());
  assert(prop.has_set_to());
  assert(prop.has_is_in_conflict());
}

/*******************************************************************\

Function: bv_refinementt::~bv_refinementt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_refinementt::~bv_refinementt()
{
}

/*******************************************************************\

Function: bv_refinementt::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt bv_refinementt::dec_solve()
{
  // do the usual post-processing
  status() << "BV-Refinement: post-processing" << eom;
  post_process();

  add_cpu_approximations();
  
  debug() << "Solving with " << prop.solver_text() << eom;

  unsigned iteration=0;

  unsigned start_inv_size=cpu_approximations.size();

//  absolute_timet sat_start=current_time();
  
  // now enter the loop
  while(true)
  {
    iteration++;

    status() << "BV-Refinement: iteration " << iteration << eom;

    // output the very same information in a structured fashion
    if(ui==ui_message_handlert::XML_UI)
    {
      xmlt xml("refinement-iteration");
      xml.data=std::to_string(iteration);
      std::cout << xml << '\n';
    }

    switch(prop_solve())
    {
    case D_SATISFIABLE:
      check_SAT();
      if(!progress)
      {
        //      absolute_timet sat_stop=current_time();
        status() << "BV-Refinement: got SAT, and it simulates => SAT" << eom;
        status() << "Total iterations: " << iteration << eom;
        status() << "CPU_REFINEMENT_END: " << start_inv_size << " to "
                 << cpu_approximations.size() << " in " << iteration << eom;
//        status() << "CPU EFINEMENT Runtime decision procedure: " << (sat_stop-sat_start) << eom;
        return D_SATISFIABLE;
      }
      else
        status() << "BV-Refinement: got SAT, and it is spurious, refining"
                 << eom;
      break;

    case D_UNSATISFIABLE:
      check_UNSAT();
      if(!progress)
      {
        //      absolute_timet sat_stop=current_time();
        status() << "BV-Refinement: got UNSAT, and the proof passes => UNSAT"
                 << eom;
        status() << "Total iterations: " << iteration << eom;
        status() << "CPU_REFINEMENT_END: " << start_inv_size << " to "
                 << cpu_approximations.size() << " in " << iteration << eom;
//        status() << "CPU REFINEMENT Runtime decision procedure: " << (sat_stop-sat_start) << eom;

        return D_UNSATISFIABLE;
      }
      else
        status() << "BV-Refinement: got UNSAT, and the proof fails, refining"
                 << eom;
      break;

    default:
      return D_ERROR;
    }
  }
}

/*******************************************************************\

Function: bv_refinementt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt bv_refinementt::prop_solve()
{
  // this puts the underapproximations into effect
  bvt assumptions=parent_assumptions;

  for(approximationst::const_iterator
      a_it=approximations.begin();
      a_it!=approximations.end();
      a_it++)
  {
    assumptions.insert(
      assumptions.end(),
      a_it->over_assumptions.begin(), a_it->over_assumptions.end());
    assumptions.insert(
      assumptions.end(),
      a_it->under_assumptions.begin(), a_it->under_assumptions.end());
  }

  assumptions.insert(assumptions.end(), cpu_approximations.begin(), cpu_approximations.end());
  
  prop.set_assumptions(assumptions);
  propt::resultt result=prop.prop_solve();
  prop.set_assumptions(parent_assumptions);

  switch(result)
  {
    case propt::P_SATISFIABLE: return D_SATISFIABLE;
    case propt::P_UNSATISFIABLE: return D_UNSATISFIABLE;
    default: return D_ERROR;
  }
}

/*******************************************************************\

Function: bv_refinementt::check_SAT

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::check_SAT()
{
  progress=false;
  
//  if (do_array_refinement) {
    arrays_overapproximated();
//  }

//  if (do_array_refinement || do_arithmetic_refinement) {
    for(approximationst::iterator
          a_it=approximations.begin();
        a_it!=approximations.end();
        a_it++)
      check_SAT(*a_it);
//  }

#ifdef COUNT_WRITE_SAVING
  if(!progress) {
    uint64_t totalWriteSaved = 0;
    for (const auto& it : solver_write_save_count_lit)
      totalWriteSaved += it.second;
    std::cout << "CPU REFINEMENT: total writes saved " << totalWriteSaved << std::endl;
  }
#endif
}

/*******************************************************************\

Function: bv_refinementt::check_UNSAT

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::check_UNSAT()
{
  progress=false;

  check_cpu_UNSAT();
  
  for(approximationst::iterator
      a_it=approximations.begin();
      a_it!=approximations.end();
      a_it++)
    check_UNSAT(*a_it);
}

/*******************************************************************\

Function: bv_refinementt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::set_to(const exprt &expr, bool value)
{
  #if 0
  unsigned prev=prop.no_variables();
  SUB::set_to(expr, value);
  unsigned n=prop.no_variables()-prev;
  std::cout << n << " EEE " << expr.id() << "@" << expr.type().id();
  forall_operands(it, expr)
    std::cout << " " << it->id() << "@" << it->type().id();
  if(expr.id()=="=" && expr.operands().size()==2)
    forall_operands(it, expr.op1())
      std::cout << " " << it->id() << "@" << it->type().id();
  std::cout << std::endl;
  #else
  SUB::set_to(expr, value);
  #endif
}

/*******************************************************************\

Function: bv_refinementt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::set_assumptions(const bvt &_assumptions)
{
  parent_assumptions=_assumptions;
  prop.set_assumptions(_assumptions);
}


void bv_refinementt::add_cpu_approximations()
{
//  symbol_tablet::symbolst symbols = ns.get_symbol_table().symbols;

  // for (const auto &it : get_symbols()) {
  //   std::cout << "CPU_REFINEMENT: acra "
  //             << it.first << " " << it.second.dimacs() << std::endl;
        
  //   if ((id2string(it.first).find("is_local") != std::string::npos)) {
  //     std::cout << "CPU_REFINEMENT: acra "
  //               << it.first << " " << it.second.dimacs() << std::endl;
  //   }
  // }

  // forall_symbols(it, ns.get_symbol_table().symbols) {
  //     std::cout << id2string(it->first) << std::endl;
  // }

  for (const auto &it : get_symbols()) {
    if ((id2string(it.first).find("is_local") == std::string::npos)) {
      continue;
    }
    cpu_approximations.push_back(it.second);
    #ifdef COUNT_WRITE_SAVING
    solver_write_save_count_lit[it.second] = solver_write_save_count[it.first];
    #endif
  }

    // std::cout << "CPU_REFINEMENT: "
    //           << it.first << " " << it.second.dimacs() << std::endl;
//  }

//   for(const auto &m : get_map().mapping)
//   {
//     const boolbv_mapt::literal_mapt &literal_map=m.second.literal_map;

//     if(literal_map.empty())
//       continue;
    
//     if ((id2string(m.first).find("is_local") == std::string::npos)) {
//       continue;
//     }

//     bvt bv;
// //    std::cout << "CPU_REFINEMENT: adding: " << m.first << " ";
    
//     for(const auto &lit : literal_map) {
//       if (!lit.is_set || lit.l.is_constant()) {
//         continue;
//       }
//       cpu_approximations.push_back(lit.l);
// //      std::cout << " " << lit.l.dimacs();
//       break;
//     }
//     //std::cout << std::endl;
//   }
  set_frozen(cpu_approximations);
  // forall_symbols(it, symbols)
  //   if((id2string(it->first).find("is_local") != std::string::npos)) {
  //     std::cout << "CPU_REFINEMENT: acra " << it->first << " "
  //               << it->second.dimacs() << std::endl;
  //     bvt bv;
  //     bv.resize(boolbv_width(it->second.type));

  //     map.get_literals(it->first,
  //                      it->second.type,
  //                      boolbv_width(it->second.type),
  //                      bv);
      
    // forall_literals(it, bv)
    //   std::cout << "CPU_REFINEMENT: add_approx() var_no: " << it->var_no() << std::endl;
    
      // std::cout << "CPU_REFINEMENT: acra "
      //           << id2string(it->first) << " "
      //           << boolbv_width(it->second.type) << " "
      //           << bv.size() << " "
      //           << std::endl;
      
      // add_cpu_approximation(bv);
  //}
}

void bv_refinementt::check_cpu_UNSAT()
{
  bvt new_approx;
  int count_conflicts = 0;

  while (!cpu_approximations.empty()) {
    literalt tmp = cpu_approximations.back();
    if (!prop.is_in_conflict(tmp)) {
      new_approx.push_back(tmp);
    } else {
      //    std::cout << "CPU REFINEMENT: check_cpu_UNSAT() "
//                << tmp.dimacs() << " is in conflict" << std::endl;
      count_conflicts++;
      #ifdef COUNT_WRITE_SAVING
      solver_write_save_count_lit[tmp] = 0;
      #endif
      progress = true;
    }
    cpu_approximations.pop_back();
  }

//  std::cout << "CPU_REFINEMENT: " << new_approx.size() << std::endl;
  
  // if (count_conflicts == 0 && new_approx.size() > 0) {
  //   for (bvt::const_iterator itr = new_approx.begin();
  //        itr != new_approx.end();
  //        itr++) {
  //     for(const auto &m : get_map().mapping)
  //     {
  //       const boolbv_mapt::literal_mapt &literal_map=m.second.literal_map;

  //       if(literal_map.empty())
  //         continue;

  //       if ((id2string(m.first).find("is_local") == std::string::npos)) {
  //         continue;
  //       }

  //       for(const auto &lit : literal_map) {
  //         if (!lit.is_set || lit.l.is_constant()) {
  //           continue;
  //         }
  //         if (*itr == lit.l) {
  //           std::cout << "CPU_REFIENEMENT: " << m.first << " " << lit.l.dimacs() << std::endl;
  //         }
  //       }
  //     }
  //   //std::cout << std::endl;
  //   }
  // }    
 std::cout << "CPU REFINEMENT: check_cpu_UNSAT() conflict count "
           << count_conflicts << std::endl;
  
  cpu_approximations.insert(cpu_approximations.end(),
                            new_approx.begin(),
                            new_approx.end());

  #ifdef COUNT_WRITE_SAVING
  if(!progress) {
    uint64_t totalWriteSaved = 0;
    for (const auto& it : solver_write_save_count)
      totalWriteSaved += it.second;
    std::cout << "CPU REFINEMENT: total writes saved " << totalWriteSaved << std::endl;
  }
  #endif
    
}
// void bv_refinementt::add_cpu_approximation(const bvt& bv)
// {
//     approximations.push_back(approximationt(approximations.size()));
//   approximationt &a = approximations.back(); // stable!
//   a.result_bv = bv;
//   a.no_operands = 0;
//   set_frozen(a.result_bv);
//   a.over_state = a.under_state = 0;

//   a.under_assumptions.reserve(a.result_bv.size());
  
//   for (std::size_t i = 0; i < a.result_bv.size(); i++) {
//     a.add_under_assumption(a.result_bv[i]);
//   }

// }

