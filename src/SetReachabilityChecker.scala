import leon.collection._
import leon.lang._
import leon.annotation._
import leon.proof._

import scala.language.postfixOps

object SetReachabilityChecker {

  case class State(registers: List[Boolean])
  
  case class System(nrOfRegisters: BigInt, transitions: List[(State, State)])
  
  abstract class Result
  case object Unknown extends Result
  case object Unreachable extends Result
  case class Trace(states: List[State]) extends Result

  def kReachabilityCheck(currentTrace: List[State], s: System, target: State, k: BigInt) : Result = {
    require(!currentTrace.isEmpty && isTrace(s, currentTrace))
    
    if(currentTrace.head == target)
      Trace(currentTrace)
    else if(k == 0)
      Unknown
    else {
      val succ = successors(s.transitions, currentTrace.head)
      exploreSuccessors(succ, currentTrace, s, target, k - 1, false)
    }
  }

  def exploreSuccessors(succ: List[State], currentTrace: List[State], s: System, target: State, k: BigInt, unknown: Boolean) : Result = {
    require(isTrace(s, currentTrace) && (currentTrace.isEmpty || succ.forall(s1 => s.transitions.contains((currentTrace.head, s1)))))
    succ match {
      case Nil() => if(unknown) Unknown else Unreachable
         case x :: xs => {
         val res = kReachabilityCheck(x :: currentTrace, s, target, k)
         res match {
           case Trace(t) => res //target found
           case Unknown => exploreSuccessors(xs, currentTrace, s, target, k, true)
           case Unreachable => exploreSuccessors(xs, currentTrace, s, target, k, unknown)
         }
      }
    }
  }

  def successors(tr: List[(State, State)], s: State) : List[State] = {
   tr match {
     case Nil() => List()
     case Cons((s1,s2), trs) =>
       if (s1 == s) Cons(s2, successors(trs, s))
       else successors(trs, s)
   }
  }
  
  def successorsTransition(tr: List[(State, State)], s: State, st: State) : Boolean = {
    require (successors(tr, s).contains(st)) 
    tr match {
      case Nil() => tr.contains((s, st))
      case x :: xs => ((successors(xs, s).contains(st) && successorsTransition(xs, s, st)) || (x._2 == st && x._1 == s)) &&
                      tr.contains((s, st))
    }
  } holds
  
  def isTrace(s: System, t: List[State]) : Boolean = {
    t match {
      case s1 :: s2 :: ts => 
        s.transitions.contains((s2, s1)) &&
        isTrace(s, s2 :: ts)
      case _ => true
    }
  }
  
  //TODO prove
  def correctTrace(s: System, initial: List[State], target: State, k: BigInt) : Boolean = {
    val res = exploreSuccessors(initial, List(), s, target, k, false)
    res match {
      case Trace(t) =>
        //initial.contains(t.last) &&
        //t.head == target && 
        isTrace(s, t)
        /*t match {
          case s1 :: s2 :: ts => 
            s.transitions.contains((s2, s1))
          case _ => true
        }*/
      case _ => true
    }
  } holds

  
}
