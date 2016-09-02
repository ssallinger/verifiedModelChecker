
import leon.collection._
import leon.lang._
import leon.annotation._
import leon.proof._

import scala.language.postfixOps

object SetReachabilityChecker {

  case class State(registers: List[Boolean]) {
    override def toString : String = {
     registers match {
       case Nil() => ";"
       case Cons(x, xs) if(x) => "1" + State(xs).toString
       case Cons(x, xs) => "0" + State(xs).toString
     }
    }
  }
  
  def hello(tr: (State,State)): String = {
    val (p,q) = tr
    p.toString + " -> " + q.toString
  }
  
  case class System(nrOfRegisters: BigInt, transitions: List[(State, State)]) {
    /*override def toString: String = transitions match {
      case Nil() => ""
      case Cons(tr,trs) =>
        hello(tr) + "\n" + System(nrOfRegisters, trs).toString
    }*/
  }
  
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
             canTransitionSucc(s.transitions, currentTrace.last) &&
             currentTrace.head == initial &&
             (currentTrace.last == target || !currentTrace.contains(target))
             //&&
             //containsForall(successors(s.transitions, currentTrace.head)) &&
             //allSuccessorsTransition(s, currentTrace.head, successors(s.transitions, currentTrace.head)) &&
             //successors(s.transitions, currentTrace.head).forall(s1 => s.transitions.contains((currentTrace.head, s1)))
     )
     
     if(currentTrace.last == target)
       Trace(currentTrace)
     else if(k == 0)
       Unknown
     else {
       // canTransition(s.transitions, currentTrace.head, successors(s.transitions, currentTrace.head))
       exploreSuccessors(successors(s.transitions, currentTrace.last), currentTrace, s, target, k - 1, false, initial)
     }
   } ensuring(res => res match {
                        case Trace(t) => isTrace(s, t) && !t.isEmpty && t.head == initial && t.last == target
                        case _ => true
                     }
   )
   
  @induct
  def prependTrace(t: List[State], s: System, st: State) : Boolean = {
    require(isTrace(s, t) && s.transitions.contains((t.last, st)))
    
    isTrace(s, t :+ st)
  } holds
  
  @induct
  def noTarget(t: List[State], target: State, x: State): Boolean = {
    require(!t.contains(target))
    
    val l = t :+ x
    
    x == l.last && (target == x || !l.contains(target))
  } holds
 
  def exploreSuccessors(succ: List[State], currentTrace: List[State], s: System, target: State, k: BigInt, unknown: Boolean, initial: State) : Result = {
    require(
      isTrace(s, currentTrace) && 
      !currentTrace.isEmpty && 
      canTransition(s.transitions, currentTrace.last, succ) && 
      currentTrace.head == initial &&
      !currentTrace.contains(target))
     
    succ match {
      case Nil() => if(unknown) Unknown else Unreachable
      case Cons(x,xs) 
        if (
          !currentTrace.contains(x) && 
          prependTrace(currentTrace, s, x) &&
          noTarget(currentTrace, target, x)
        ) => {
       
          val res = kReachabilityCheck(currentTrace :+ x, s, target, k, initial)
          res match {
            case Trace(t) => res //target found
            case Unknown => exploreSuccessors(xs, currentTrace, s, target, k, true, initial)
            case Unreachable => exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
          }
       }
       case Cons(_,xs) => exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
     }
   } ensuring(res => res match {
                        case Trace(t) => isTrace(s, t) && !t.isEmpty && t.head == initial && t.last == target
                        case _ => true
                     }
   )
  
  
   def isTrace(s: System, t: List[State]) : Boolean = {
     t match {
       case s1 :: s2 :: ts => 
         s.transitions.contains((s1, s2)) &&
         isTrace(s, s2 :: ts)
       case _ => true
     }
   }
   
   def correctTrace(s: System, initial: State, target: State, k: BigInt) : Boolean = {
     val res = kReachabilityCheck(List(initial), s, target, k, initial)
     
     res match {
       case Trace(t) =>
         initial == t.head &&
         t.last == target && 
         isTrace(s, t)
       case _ => true
     }
   } holds
   
   @induct
   def inSuccessors(tr: List[(State, State)], s1: State, s2: State) : Boolean = {
    require(tr.contains((s1, s2)))
    successors(tr, s1).contains(s2)
   } holds
   
  def disjoint[X](l1: List[X], l2: List[X]): Boolean = {
    (l1.content & l2.content).isEmpty
  }
  
  def unique[X](l: List[X]): Boolean = l match {
    case Nil() => true
    case Cons(x,xs) => !xs.contains(x) && unique(xs)
  }
   
  def contentContains[X](l: List[X], x: X): Boolean = {
    require(l.contains(x))
    
    l.content.contains(x)
  } holds
   
   def completeTrace(l: List[State], s: System, initial: State, target: State, currentTrace: List[State]) : Boolean = {
     require(
      isTrace(s, l) && 
      !l.isEmpty && 
      l.last == target && 
      !currentTrace.isEmpty && 
      l.head == currentTrace.last && 
      isTrace(s, currentTrace) &&
      currentTrace.head == initial &&
      canTransitionSucc(s.transitions, currentTrace.last) &&
      (currentTrace.last == target || !currentTrace.contains(target)) &&
      disjoint(currentTrace, l.tail) &&
      unique(l)
     )
     val res = kReachabilityCheck(currentTrace, s, target, l.length-1, initial)
     
     (
     if(currentTrace.last == target)
       res match {
        case Trace(_) => true
        case _ => false
       }
     else if(l.length-1 == 0)
       false
     else {
       // canTransition(s.transitions, currentTrace.head, successors(s.transitions, currentTrace.head))
       //exploreSuccessors(successors(s.transitions, currentTrace.head), currentTrace, s, target, k - 1, false, initial)
        val succ = successors(s.transitions, currentTrace.last)
        
        if(inSuccessors(s.transitions, l.head, l.tail.head)){
          completeTraceExploreSucc(l.tail, s, succ, target, false, initial, currentTrace) /*&&
          (res match {
            case Trace(_) => true
            case _ => false
           })*/
        } else
          false
        //completeTraceExploreSucc(l.tail, s, succ, target, false, initial, currentTrace)
     }) &&  (res match {
      case Trace(_) => true
      case _ => false
    })
     
   } holds
   
   
  def completeTraceExploreSucc(l: List[State], s: System, succ: List[State], target: State, unknown: Boolean, initial: State, currentTrace: List[State]) : Boolean = {
      require(
        isTrace(s, l) && 
        !l.isEmpty && 
        l.last == target && 
        !currentTrace.isEmpty && 
        succ.contains(l.head) && 
        isTrace(s, currentTrace) &&
        currentTrace.head == initial && 
        canTransition(s.transitions, currentTrace.last, succ) &&
        !currentTrace.contains(target) &&
        disjoint(currentTrace, l) &&
        unique(l)
      )  
     
    val res = exploreSuccessors(succ, currentTrace, s, target, l.length-1, unknown, initial)

     
    (succ match {
      case Nil() => false
      case Cons(x,xs) if (!currentTrace.contains(x)) =>
        if (prependTrace(currentTrace, s, x) &&
          noTarget(currentTrace, target, x)) {
      
      
          kReachabilityCheck(currentTrace :+ x, s, target, l.length-1, initial) match {
            case Trace(t) => res match {
              case Trace(_) => true
              case _ => false
            } //target found
            case Unknown =>  
              if(x == l.head) {
                completeTrace(l, s, initial, target, currentTrace :+ x) /*&&
                false*/
              } else
                completeTraceExploreSucc(l, s, xs, target, true, initial, currentTrace)/*&& (res match {
              case Trace(_) => true
              case _ => false
            })*/ //exploreSuccessors(xs, currentTrace, s, target, k, true, initial)
            case Unreachable => if(x == l.head) {
                completeTrace(l, s, initial, target, currentTrace :+ x) /*&&
                false*/
              } else
                completeTraceExploreSucc(l, s, xs, target, unknown, initial, currentTrace)//exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
          }
        } else false
         
       case Cons(x,xs) => //exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
                          if(x == l.head)
                            //currentTrace.contains(x) &&
                            //contentContains(currentTrace,x) &&
                            //currentTrace.content.contains(x) &&
                            false
                          else {
                            completeTraceExploreSucc(l, s, xs, target, unknown, initial, currentTrace)
                          }
     }) &&  (res match {
      case Trace(_) => true
      case _ => false
    })
  }  holds

   
  def statesToString(l: List[State]): String = l match {
    case Nil() => ""
    case Cons(x,xs) => x.toString + "\n" + statesToString(xs)
  }
   
//  def uniqueTrace(s: System, l: List[State]): List[State] = {
    
 // } ensuring { (res: List[State]) => res.head = l.head && isTrace(s, res) && 
   
   def completeTraceInit(l: List[State], s: System, initial: State, target: State) : Boolean = {
     require(
      isTrace(s, l) && 
      !l.isEmpty && 
      l.last == target && 
      canTransitionSucc(s.transitions, initial) &&
      l.head == initial &&
      unique(l)
     )
     val res = kReachabilityCheck(List(initial), s, target, l.length-1, initial)
     
     completeTrace(l,s,initial,target,List(initial)) &&
     (res match {
      case Trace(_) => true
      case _ => false
    })
     
   } holds
   
   

}
