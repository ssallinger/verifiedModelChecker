import leon.collection._
import leon.lang._

import scala.language.postfixOps

object CTL {

  case class Atom(i: BigInt)

  abstract class Formula
  
  case class Prop(a: Atom) extends Formula
  case class And(f1: Formula, f2: Formula) extends Formula
  case class EG(f: Formula) extends Formula
  
  
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
  
  
  def always_aux(a: Automaton, p: Path, f: Formula, i: BigInt): Boolean = {
    valid(a, p(i), f) && always_aux(a, p, f, i+1)
  } holds
  
  def always(a: Automaton, p: Path, f: Formula): Boolean = always_aux(a, p, f, 0)
  
  
  def sometime_aux(a: Automaton, p: Path, f: Formula, i: BigInt): Boolean = {
    valid(a, p(i), f) || sometime_aux(a, p, f, i+1)
  } holds
  
  def sometime(a: Automaton, p: Path, f: Formula): Boolean = sometime_aux(a, p, f, 0)
  
  
  def correctPath_aux(a: Automaton, p: Path, i: BigInt): Boolean = {
    a.tr.contains((p.h(i), p.h(i+1))) && correctPath_aux(a, p, i+1)
  }
  
  def correctPath(a: Automaton, p: Path, s: State): Boolean = correctPath_aux(a, p, 0) && p(0) == s
  
  
  def valid(a: Automaton, s: State, f: Formula): Boolean = {
    f match {
      case Prop(a) => s.atoms.contains(a)
      case And(f1,f2) => valid(a, s, f1) && valid(a, s, f2)
      case EG(g) => 
        !forall((p: Path) => (correctPath(a, p, s) ==>  !always(a, p, g)))
        // exists((p: Path) => correctPath(a,p,s) && always(a, p, g))
    } 
  } holds
  
}