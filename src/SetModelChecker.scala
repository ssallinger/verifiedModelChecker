import leon.collection._
import leon.lang._
import leon.annotation._

import CTL._

import scala.language.postfixOps

object ModelChecker {

  @induct
  def filterKeepsElements[T](l: List[T], e: T, p: T => Boolean) = {
    require(l.contains(e) && p(e))
    
    l.filter(p).contains(e)
  } holds
  
  /*@induct
  def filterRemovesElements[T](l: List[T], e: T, p: T => Boolean) = {
    require(!p(e))
    
    !l.filter(p).contains(e)
  } holds*/

  def sat(a: Automaton, f: Formula): Set[State] = {
    f match {
      case True    => a.states.content
      case False   => Set()
      case Prop(atom) => a.states.filter(s => s.atoms.contains(atom)).content
      case And(f1, f2) =>
        val b1 = sat(a, f1)
        val b2 = sat(a, f2)
        b1 & b2
      /*case Or(f1, f2) =>
        val b1 = sat(a, f1)
        val b2 = sat(a, f2)
        b1 ++ b2
      case Not(f1) => a.states.content -- sat(a, f1)*/

      
//         build(states.b, Variable(atom.i))
//       }
//       case Not(f1) => {
//         val bdd = sat(states, transitions, f1)
//         minus(bdd.b, states.root, bdd.root)
//       }
//       case And(f1, f2) => {
//         val b1 = sat(states, transitions, f1)
//         val b2 = sat(RootedBDD(b1.b, states.root), transitions, f2)
//         intersect(b2.b, b1.root, b2.root)
//       }
//       case Or(f1, f2) => {
//         val b1 = sat(states, transitions, f1)
//         val b2 = sat(RootedBDD(b1.b, states.root), transitions, f2)
//         union(b2.b, b1.root, b2.root)
//       }
//       case Implies(f1, f2) => sat(states, transitions, Or(f1, Not(f2)))
//       //case AX(f1)          => sat(states, transitions, Not(EX(Not(f1))))
//       case EX(f1)          => satex(states, transitions, f1)
//       //case AU(f1, f2)      => sat(states, transitions, Not(Or(EU(Not(f2), And(Not(f1), Not(f2))), EG(Not(f2)))))
//       case EU(f1, f2)      => sateu(states, transitions, f1, f2)
//       //case EF(f1)          => sat(states, transitions, EU(Top(), f1))
//       case EG(f1)          => sateg(states, transitions,f1)
      //case AF(f1)          => sat(states, transitions, Not(EG(Not(f1))))
      //case AG(f1)          => sat(states, transitions, Not(EF(Not(f1))))
    }
  }
  
  def validToSat(a: Automaton, s: State, f: Formula): Boolean = {
    require(a.states.contains(s) && valid(a, s, f))
    
    f match {
      case True => sat(a,f).contains(s)
      case False => sat(a,f).contains(s) 
      case Prop(atom) => 
        filterKeepsElements(a.states, s, (s: State) => s.atoms.contains(atom)) && 
        sat(a,f).contains(s)
      case And(f1, f2) => 
        validToSat(a, s, f1) &&
        validToSat(a, s, f2) && 
        sat(a,f).contains(s)
      /*case Or(f1, f2) => 
        ((valid(a,s,f1) && validToSat(a, s, f1)) ||
        (valid(a,s,f2) && validToSat(a, s, f2))) &&        
        sat(a,f).contains(s)
      case Not(f1) => 
        !valid(a, s, f1) &&
        //!(sat(a, f1).contains(s)) &&
        satToValid(a, s, f1) &&
        sat(a,f).contains(s)*/
    }
  } holds
  
  @library
  def satToValid(a: Automaton, s: State, f: Formula): Boolean = {
    require(a.states.contains(s) && !valid(a, s, f))
  
    !sat(a, f).contains(s)
    
  } holds
  
  //EG, EU, EX form minimal adequate subset of temporal connectives
  //TODO implement
//   def satex(states: RootedBDD, transitions: RootedBDD, f: Formula): RootedBDD = states
//   def sateu(states: RootedBDD, transitions: RootedBDD, f1: Formula, f2: Formula): RootedBDD = states //see book
//   def sateg(states: RootedBDD, transitions: RootedBDD, f: Formula): RootedBDD = states //see Isabelle tutorial

}
