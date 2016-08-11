import leon.collection._
import leon.lang._

import sharedOBDDs._
import CTL._

object ModelChecker {
  def root(b: (BDD, BigInt)) = b._2
  def bdd(b: (BDD, BigInt)) = b._1

  def sat(states: (BDD, BigInt), transitions: (BDD, BigInt), f: Formula): (BDD, BigInt) = {
    f match {
      case True    => states
      case False => (bdd(states), 0)
      case Prop(atom) => {
        build(bdd(states), Variable(atom.i))
      }
      case Not(f1) => {
        val b = sat(states, transitions, f1)
        minus(bdd(b), root(states), root(b))
      }
      case And(f1, f2) => {
        val b1 = sat(states, transitions, f1)
        val b2 = sat((bdd(b1), root(states)), transitions, f2)
        intersect(bdd(b2), root(b1), root(b2))
      }
      case Or(f1, f2) => {
        val b1 = sat(states, transitions, f1)
        val b2 = sat((bdd(b1), root(states)), transitions, f2)
        union(bdd(b2), root(b1), root(b2))
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
  def satex(states: (BDD, BigInt), transitions: (BDD, BigInt), f: Formula): (BDD, BigInt) = states
  def sateu(states: (BDD, BigInt), transitions: (BDD, BigInt), f1: Formula, f2: Formula): (BDD, BigInt) = states //see book
  def sateg(states: (BDD, BigInt), transitions: (BDD, BigInt), f: Formula): (BDD, BigInt) = states //see Isabelle tutorial

}

