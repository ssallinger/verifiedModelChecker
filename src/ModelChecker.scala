import leon.collection._
import leon.lang._

import sharedOBDDs._

object ModelChecker {
  //CTL formula
  sealed abstract class Formula
  case class Top() extends Formula
  case class Bottom() extends Formula
  case class Atom(id: Int) extends Formula
  case class Not(f: Formula) extends Formula
  case class And(f1: Formula, f2: Formula) extends Formula
  case class Or(f1: Formula, f2: Formula) extends Formula
  case class Implies(f1: Formula, f2: Formula) extends Formula
  case class AX(f: Formula) extends Formula
  case class EX(f: Formula) extends Formula
  case class AU(f1: Formula, f2: Formula) extends Formula
  case class EU(f1: Formula, f2: Formula) extends Formula
  case class EF(f: Formula) extends Formula
  case class EG(f: Formula) extends Formula
  case class AF(f: Formula) extends Formula
  case class AG(f: Formula) extends Formula


  def root(b: (BDD, Int)) = b._2
  def bdd(b: (BDD, Int)) = b._1

  def sat(states: (BDD, Int), transitions: (BDD, Int), f: Formula): (BDD, Int) = {
    f match {
      case Top()    => states
      case Bottom() => (bdd(states), 0)
      case Atom(id) => {
        build(bdd(states), Variable(id))
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
      case AX(f1)          => sat(states, transitions, Not(EX(Not(f1))))
      case EX(f1)          => satex(states, transitions, f1)
      case AU(f1, f2)      => sat(states, transitions, Not(Or(EU(Not(f2), And(Not(f1), Not(f2))), EG(Not(f2)))))
      case EU(f1, f2)      => sateu(states, transitions, f1, f2)
      case EF(f1)          => sat(states, transitions, EU(Top(), f1))
      case EG(f1)          => sateg(states, transitions,f1)
      case AF(f1)          => sat(states, transitions, Not(EG(Not(f1))))
      case AG(f1)          => sat(states, transitions, Not(EF(Not(f1))))
    }
  }
  
  //EG, EU, EX form minimal adequate subset of temporal connectives
  //TODO implement
  def satex(states: (BDD, Int), transitions: (BDD, Int), f: Formula): (BDD, Int) = states
  def sateu(states: (BDD, Int), transitions: (BDD, Int), f1: Formula, f2: Formula): (BDD, Int) = states //see book
  def sateg(states: (BDD, Int), transitions: (BDD, Int), f: Formula): (BDD, Int) = states //see Isabelle tutorial

}

