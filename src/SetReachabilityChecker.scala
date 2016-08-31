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
    require(!currentTrace.isEmpty &&
            isTrace(s, currentTrace) &&
            //containsForall(successors(s.transitions, currentTrace.head)) &&
            allSuccessorsTransition(s, currentTrace.head, successors(s.transitions, currentTrace.head)) &&
            successors(s.transitions, currentTrace.head).forall(s1 => s.transitions.contains((currentTrace.head, s1)))
    )
    
    if(currentTrace.head == target)
      Trace(currentTrace)
    else if(k == 0)
      Unknown
    else {
      exploreSuccessors(successors(s.transitions, currentTrace.head), currentTrace, s, target, k - 1, false)
    }
  }
  
  //@ignore
  def containsForall(l: List[State]) : Boolean = {
    l match {
      case Nil() => l.forall(x => l.contains(x))
      case x :: xs => l.contains(x) && containsForall(xs) && xs.forall(y => l.contains(y)) && l.forall(y => l.contains(y))
    }
    //l.forall(x => l.contains(x))
  } holds
  
  //TODO
  def listContainsTail[X](l :List[X]) : Boolean = {
    l match {
      case Nil() => trivial
      case x :: xs => true
    }
    
  } holds

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
  
  def allSuccessorsTransition(sys: System, s: State, res: List[State]) : Boolean = {
    require(res.forall(st => successors(sys.transitions, s).contains(st)))
    res match {
      case Nil() => res.forall(st => sys.transitions.contains((s, st)))
      case x :: xs => allSuccessorsTransition(sys, s, xs) &&
                      successors(sys.transitions, s).contains(x) &&
                      successorsTransition(sys.transitions, s, x) &&
                      res.forall(st => sys.transitions.contains((s, st)))
    }
  } holds
  
  def test(res: List[State]) : Boolean = {
    res match {
      case Nil() => trivial
      case x :: xs => test(xs) && res.forall(st => true)
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
