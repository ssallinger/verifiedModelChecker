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
  
  
  def canTransition(tr: List[(State,State)], x: State, l: List[State]): Boolean = {
    l match {
      case Nil() => true
      case Cons(y,ys) => tr.contains((x,y)) && canTransition(tr, x, ys)
    }
  }
  
  
  def canTransitionSuccHelp(tr: List[(State,State)], s: State, succ: List[State]): Boolean = {
    //val succ = successors(tr,s)
    
    require(subset(succ, successors(tr,s)))
    succ match {
      case Nil() => true
      case Cons(x, xs) => successorsTransition(tr, s, x) && tr.contains((s,x)) && canTransitionSuccHelp(tr, s, xs) && canTransition(tr, s, succ)
    }
    //canTransition(tr, s, succ)
  } holds
  
  def canTransitionSucc(tr: List[(State,State)], s: State): Boolean = {
    val succ = successors(tr,s)
    
    subsetReflexive(succ) &&
    canTransitionSuccHelp(tr, s, succ) &&
    canTransition(tr, s, succ)
    
  } holds
  
  def subset[X](l1: List[X], l2: List[X]) : Boolean = {
    l1 match {
      case Nil() => true
      case Cons(x, xs) => l2.contains(x) && subset(xs,  l2)
    }
  }
  
  def subsetReflexive[X](l1: List[X]) : Boolean = {
    l1 match {
      case Nil() => true
      case Cons(x, xs) => l1.contains(x) && subsetReflexive(xs) && subsetExtend(xs, xs, x) && subset(xs, l1) && subset(l1, l1)
      //wissen: 
    }
    //subset(l1, l1)
  } holds
  
  @induct
  def subsetExtend[X](l1: List[X], l2: List[X], x: X) : Boolean = {
    require(subset(l1, l2))
    
    subset(l1, x :: l2)
  } holds

   def kReachabilityCheck(currentTrace: List[State], s: System, target: State, k: BigInt, initial: State) : Result = {
     require(!currentTrace.isEmpty &&
             isTrace(s, currentTrace) &&
             canTransitionSucc(s.transitions, currentTrace.head) &&
             currentTrace.last == initial
             //&&
             //containsForall(successors(s.transitions, currentTrace.head)) &&
             //allSuccessorsTransition(s, currentTrace.head, successors(s.transitions, currentTrace.head)) &&
             //successors(s.transitions, currentTrace.head).forall(s1 => s.transitions.contains((currentTrace.head, s1)))
     )
     
     if(currentTrace.head == target)
       Trace(currentTrace)
     else if(k == 0)
       Unknown
     else {
       // canTransition(s.transitions, currentTrace.head, successors(s.transitions, currentTrace.head))
       exploreSuccessors(successors(s.transitions, currentTrace.head), currentTrace, s, target, k - 1, false, initial)
     }
   } ensuring(res => res match {
                        case Trace(t) => isTrace(s, t) && !t.isEmpty && t.last == initial && t.head == target
                        case _ => true
                     }
   )
 
   def exploreSuccessors(succ: List[State], currentTrace: List[State], s: System, target: State, k: BigInt, unknown: Boolean, initial: State) : Result = {
     require(isTrace(s, currentTrace) && !currentTrace.isEmpty && canTransition(s.transitions, currentTrace.head, succ) && currentTrace.last == initial)
     
     succ match {
       case Nil() => if(unknown) Unknown else Unreachable
       case Cons(x,xs) if (!currentTrace.contains(x))=>{
       
          val res = kReachabilityCheck(x :: currentTrace, s, target, k, initial)
          res match {
            case Trace(t) => res //target found
            case Unknown => exploreSuccessors(xs, currentTrace, s, target, k, true, initial)
            case Unreachable => exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
          }
       }
       case Cons(_,xs) => exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
     }
   } ensuring(res => res match {
                        case Trace(t) => isTrace(s, t) && !t.isEmpty && t.last == initial && t.head == target
                        case _ => true
                     }
   )
  
  
   def isTrace(s: System, t: List[State]) : Boolean = {
     t match {
       case s1 :: s2 :: ts => 
         s.transitions.contains((s2, s1)) &&
         isTrace(s, s2 :: ts)
       case _ => true
     }
   }
   
   def correctTrace(s: System, initial: State, target: State, k: BigInt) : Boolean = {
     val res = kReachabilityCheck(List(initial), s, target, k, initial)
     res match {
       case Trace(t) =>
         initial == t.last &&
         t.head == target && 
         isTrace(s, t)
       case _ => true
     }
   } holds

}
