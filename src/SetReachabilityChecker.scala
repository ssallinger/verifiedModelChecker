import leon.collection._
import leon.lang._
import leon.annotation._
import leon.proof._

import scala.language.postfixOps

object SetReachabilityChecker {

  case class State(registers: List[Boolean])
  
  case class System(nrOfRegisters: BigInt, transitions: List[(State, State)])
  
  def reachable(s: System, initial: List[State], target: List[State]) : Boolean = {
    initial.exists(i => successors(s.transitions, i).exists(i2 =>
      target.contains(i2) ||
      reachable(s, i2 :: initial, target)))
  }
  
  
  def reachabilityCheck(s: System, initial: Set[State], target: Set[State]) : Boolean = {
    if((initial & target) != Set[State]())
      true
    else {
      val n = next(s, initial) ++ initial
      if((n subsetOf initial) && (initial subsetOf n))
        false
      else
        reachabilityCheck(s, n, target)
    }  
  }
  
  def next(s: System, states: Set[State]) : Set[State] = {
    //union over successors of all states
    setToList(states).map(st => successors(s.transitions, st).content).foldLeft(Set[State]())(_++_)
  }
  
  def successors(tr: List[(State, State)], s: State) : List[State] = {
    tr match {
      case Nil() => List()
      case Cons((s1,s2), trs) =>
        if (s1 == s) Cons(s2, successors(trs, s))
        else successors(trs, s)
    }
  } 
  
  def correctChecker(s: System, initial: List[State], target: List[State]) : Boolean = {
    reachable(s, initial, target) == reachabilityCheck(s, initial.content, target.content) //should reachable use unique lists?
  } holds
  
}
