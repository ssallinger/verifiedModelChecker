import leon.collection._
import leon.lang._
import leon.annotation._
import leon.proof._

import scala.language.postfixOps

import sharedOBDDs._

object ReachabilityChecker {

  case class Registers(values: List[Boolean])
  
  case class State(registers: Registers)
  
  case class System(registers: Registers, circuit: Expression)
  
  def reachable(s: System, initial : Set[State], target : Set[State]) : Boolean = {
    //???
    false
  }
  
  def reachabilityCheck(b: BDD, transitions: BigInt, initialStates: BigInt, targetStates: BigInt) : Boolean = {
    if(intersect(b, initialStates, targetStates).root != 0)
      true
    else {
      val successors = post(b, initialStates, transitions)
      val next = union(successors.b, initialStates, successors.root)
      if(next.root == initialStates) //fixed point
        false
      else
        reachabilityCheck(next.b, transitions, next.root, targetStates)
    }
  }
  
  

}
