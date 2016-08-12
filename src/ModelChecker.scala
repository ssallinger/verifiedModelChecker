import leon.collection._
import leon.lang._

import sharedOBDDs._
import CTL._

object ModelChecker {

   def sat(states: RootedBDD, transitions: RootedBDD, f: Formula): RootedBDD = {
    f match {
      case True    => states
      case False => RootedBDD(states.b, 0)
      case Prop(atom) => {
        build(states.b, Variable(atom.i))
      }
      case Not(f1) => {
        val bdd = sat(states, transitions, f1)
        minus(bdd.b, states.root, bdd.root)
      }
      case And(f1, f2) => {
        val b1 = sat(states, transitions, f1)
        val b2 = sat(RootedBDD(b1.b, states.root), transitions, f2)
        intersect(b2.b, b1.root, b2.root)
      }
      case Or(f1, f2) => {
        val b1 = sat(states, transitions, f1)
        val b2 = sat(RootedBDD(b1.b, states.root), transitions, f2)
        union(b2.b, b1.root, b2.root)
      }
      case Implies(f1, f2) => sat(states, transitions, Or(f1, Not(f2)))
      //case AX(f1)          => sat(states, transitions, Not(EX(Not(f1))))
      case EX(f1)          => satex(states, transitions, f1)
      //case AU(f1, f2)      => sat(states, transitions, Not(Or(EU(Not(f2), And(Not(f1), Not(f2))), EG(Not(f2)))))
      case EU(f1, f2)      => sateu(states, transitions, f1, f2)
      //case EF(f1)          => sat(states, transitions, EU(Top(), f1))
      case EG(f1)          => sateg(states, transitions,f1)
      //case AF(f1)          => sat(states, transitions, Not(EG(Not(f1))))
      //case AG(f1)          => sat(states, transitions, Not(EF(Not(f1))))
    }
  }
  
  //EG, EU, EX form minimal adequate subset of temporal connectives
  //TODO implement
  def satex(states: RootedBDD, transitions: RootedBDD, f: Formula): RootedBDD = states
  def sateu(states: RootedBDD, transitions: RootedBDD, f1: Formula, f2: Formula): RootedBDD = states //see book
  def sateg(states: RootedBDD, transitions: RootedBDD, f: Formula): RootedBDD = states //see Isabelle tutorial

}

