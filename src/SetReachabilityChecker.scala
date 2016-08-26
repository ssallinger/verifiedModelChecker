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
  
  def reachableSet(s: System, initial: Set[State], x: Set[State]) : Set[State]  = { //parameter x not neccessary, just for clarity
    val next = initial ++ post(s, x)
    if((next subsetOf x) && (x subsetOf next)) //fixed point
      x
    else
      reachableSet(s, initial, next)
  }
  
  def reachabilityCheck(s: System, initial: Set[State], target: Set[State]) : Boolean = {
    val reachable = reachableSet(s, initial, Set[State]())
    (reachable & target) != Set[State]()
  }
  
  /*def reachabilityCheck(s: System, initial: Set[State], target: Set[State]) : Boolean = {
    if((initial & target) != Set[State]())
      true
    else {
      val next = post(s, initial) ++ initial
      if((next subsetOf initial) && (initial subsetOf next))
        false
      else
        reachabilityCheck(s, next, target)
    }  
  }*/
  
  def post(s: System, states: Set[State]) : Set[State] = {
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
  
  def reachableToCheck(s: System, initial: List[State], target: List[State]) : Boolean = {
    require(reachable(s, initial, target))//should reachable use unique lists?
    
    reachabilityCheck(s, initial.content, target.content) 
  } holds
  
  def checkToReachable(s: System, initial: List[State], target: List[State]) : Boolean = {
    require(reachabilityCheck(s, initial.content, target.content))//should reachable use unique lists?
    
    reachable(s, initial, target)
  } holds
  
}
