import leon.collection._
import leon.lang._
import leon.annotation._
import leon.proof._

import scala.language.postfixOps

import sharedOBDDs._

object SetReachabilityChecker {

  case class Registers(values: List[Boolean])
  
  case class State(registers: Registers)
  
  case class System(registers: Registers, circuit: Expression)
  
  def reachable(s: System, initial : Set[State], target : Set[State]) : Boolean = {
    //???
    false
  }
  
  
  def reachabilityCheck(s: System, initialStates: Set[State], target: Set[State]) : Boolean = {
    if((initialStates & target) != Set[State]())
      true
    else {
      val n = next(s, initialStates) ++ initialStates
      if((n subsetOf initialStates) && (initialStates subsetOf n))
        false
      else
        reachabilityCheck(s, n, target)
    }  
  }
  
  def next(s: System, states: Set[State]) : Set[State] = {
    //union over successors of all states
    setToList(states).map(st => successors(s, st)).foldLeft(Set[State]())(_++_)
  }
  
  //TODO implement
  def successors(s: System, state: State) : Set[State] = Set[State]() 

}
