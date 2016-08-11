import leon.collection._
import leon.lang._

import scala.language.postfixOps

object CTL {

  case class Atom(i: BigInt)

  abstract class Formula
  
  case object True extends Formula
  case object False extends Formula
  case class Prop(a: Atom) extends Formula
  case class And(f1: Formula, f2: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Or(f1: Formula, f2: Formula) extends Formula
  case class Implies(f1: Formula, f2: Formula) extends Formula
  case class EX(f: Formula) extends Formula
  case class EG(f: Formula) extends Formula
  case class EU(f1: Formula, f2: Formula) extends Formula
  /*
  case class AX(f: Formula) extends Formula
  case class AU(f1: Formula, f2: Formula) extends Formula
  case class EF(f: Formula) extends Formula
  case class AF(f: Formula) extends Formula
  case class AG(f: Formula) extends Formula
  */
  case class State(atoms: Set[Atom])
  
  case class Automaton(tr: List[(State,State)]) 
  
  case class Path(h: Map[BigInt, State]) {
    def apply(i: BigInt) = h(i)
  }
  
  def post(s: State, tr: List[(State,State)]): List[State] = {
    tr match {
      case Nil() => List()
      case Cons((s1,s2), trs) =>
        if (s1 == s) Cons(s2, post(s, trs))
        else post(s, trs)
    }
  }
  
  
  def pre(s: State, tr: List[(State,State)]): List[State] = {
    tr match {
      case Nil() => List()
      case Cons((s1,s2), trs) =>
        if (s2 == s) Cons(s1, post(s, trs))
        else post(s, trs)
    }
  }
  
  
  def canLoop(a: Automaton, states: List[State], g: Formula): Boolean = {
    states.exists(s => 
      post(s, a.tr).exists(s2 => 
        states.contains(s2) || 
        (valid(a, s2, g) && canLoop(a, s2 :: states, g))
      )
    )
  }
  
  
  def valid(a: Automaton, s: State, f: Formula): Boolean = {
    f match {
      case Prop(a) => s.atoms.contains(a)
      case And(f1,f2) => valid(a, s, f1) && valid(a, s, f2)
      case EG(g) => valid(a, s, g) && canLoop(a, List(s), g)
    } 
  }
  
}
