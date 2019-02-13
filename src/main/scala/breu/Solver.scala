package breu;

import org.sat4j.core._
import org.sat4j.specs._
import org.sat4j.minisat._
import org.sat4j.tools._
import java.io.FileInputStream
import java.io.ObjectInputStream
import java.io.File
import Timer._
import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.ListBuffer


//
//  Allocates bits for the solver
//
class Allocator {
  // Leave room for ONEBIT (1) and ZEROBIT (2)
  var next = 3

  def reset = {
    next = 3
  }

  def alloc(count : Int) = {
    val ret = next
    next = next + count
    ret
  }
}


/**
  * Three different result types
  * UKNOWN generally indicates an error
  */
object Result extends Enumeration {
  type Result = Value
  val SAT, UNSAT, UNKNOWN = Value
}


class Stats {
  val stats = ListBuffer() : ListBuffer[String]

  def addEntry(s : String) = {
    stats += s
  }

  def clear = stats.clear

  override def toString = {
    stats.mkString("\n")
  }
}

/*
 * An abstract BREUSolver
 * 
 * Requires solveaux and unsatCore to be defined
 * 
 */
// TODO: We used to have a timeoutChecker, it now replaced by a fixed timeout.
//
// Maybe the other way is preferable, but I have not found a
// convenient way to abort sat4j. Maybe running one thread which polls
// the timeoutchecker and then sends and abort to sat4j is possible..
abstract class Solver[Term, Fun](debug : Boolean) {

  // TODO: Maybe construct better way of keeping track of time?

  var START_TIME : Long = System.currentTimeMillis
  // TODO: Currently we have 1 minute to create problems
  var MAX_TIME : Long = 60000

  type TermDomains = Map[Term, Set[Term]]
  type TermEq = (Fun, Seq[Term], Term)
  type TermGoal = Seq[Seq[(Term, Term)]]

  // Bit manipulation
  val alloc = new Allocator
  val ZEROBIT = 1
  val ONEBIT = 2    
  
  // TODO: Make real bound?
  val solver = SolverFactory.newDefault()
  val MAXVAR = 1000000;
  solver.newVar(MAXVAR);
  solver.setTimeout(1)
  val gt = new GateTranslator(solver)

  val S = new Stats
  var curId = 0
  var previousInstance = None : Option[Instance[Term, Fun]]

  val positiveBlockingClauses = ListBuffer() : ListBuffer[List[(Int,Int)]]
  val negativeBlockingClauses = ListBuffer() : ListBuffer[List[(Int,Int)]]    

  def getStat(result : breu.Result.Result) : String

  def dprint(str : String) =
    if (debug)
      print(str)

  def dprintln(str : String) =
    if (debug)
      println(str)  


  def satSolve() : Boolean = {
    checkTO()
    val REM_TIME = MAX_TIME - (System.currentTimeMillis - START_TIME)
    solver.setTimeoutMs(REM_TIME)
    try {
      solver.isSatisfiable()
    } catch {
      case e : Exception =>{
        dprintln("satSolve() timeout!")
        throw e
      }
    }
  }

  def checkTO() = {
    val CUR_TIME = System.currentTimeMillis
    if (CUR_TIME - START_TIME >= MAX_TIME) {
      dprintln("checkTO() timeout!")
      throw new org.sat4j.specs.TimeoutException
    }
  }

  def solve(problem : Problem, timeout : Long, asserted : Boolean = false) = 
  Timer.measure("Solver.solve") {

    START_TIME = System.currentTimeMillis
    MAX_TIME = timeout

    val result = 
    try {
        // if (problem.solvable == false) {
        //   println("\tDisequality check")
        //   // println(problem)
        //   (breu.Result.UNSAT, None)
        // } else {
        solveaux(problem)
      // }
    } catch {
      case e : org.sat4j.specs.ContradictionException => {
        (breu.Result.UNSAT, None)
      }

      case e : org.sat4j.specs.TimeoutException => {
        (breu.Result.UNKNOWN, None)        
      }
    }

    if (asserted) {
      result match {
        case (breu.Result.SAT, Some(model)) => {
          if (!problem.verifySolution(model)) {
            throw new Exception("False SAT")
          } else {
            // println("\t\tSAT asserted")
            (breu.Result.SAT, Some(model))
          }
        }
        case (breu.Result.UNSAT, _) => {
          // println("\t\tUNSAT *not* asserted")
          (breu.Result.UNSAT, None)
        }
        case _ => throw new Exception("Strange result from solve!")
      }
    } else {
      result
    }
  }

  def unsatCore(problem : Problem, timeout : Int) = {
    val core =
      unsatCoreAux(problem, timeout)
    assert(!core.isEmpty)
    (for (p <- core) yield (problem.order(p)))
  }

  // Asbtract functions
  protected def solveaux(problem : Problem) : 
      (Result.Result, Option[Map[Int, Int]])

  def unsatCoreAux(problem : Problem, timeout : Int) : Seq[Int]

  def reset = {
    solver.reset()
    alloc.reset
    solver.addClause(new VecInt(Array(-ZEROBIT)))
    solver.addClause(new VecInt(Array(ONEBIT)))
    S.clear
  }

  def assignmentsToSolution[Term](assignments : Map[Int, Seq[Int]]) = {
    // If bit B is true, bitArray(bitMap(B)) should be true
    var bitMap = Map() : Map[Int, List[Int]]

    // Prune all bits that are not with var ass and put in bitArray
    // (assuming all terms are represented by the same number of bits)
    var bitArray =
      Array.ofDim[Boolean](assignments.size * assignments.head._2.size)

    // Current position in bitArray
    var curPos = 0

    // Term T can find its bits in resultMap(T)
    val resultMap = 
      (for ((term, bits) <- assignments) yield {
        val newResult =
          (for (i <- 0 until bits.length) yield {
            val newList = curPos :: (bitMap.getOrElse(bits(i), List()))
            bitMap += (bits(i) -> newList)
            curPos += 1
            (curPos - 1)
          })
        term -> newResult
      })    

    for (i <- solver.model) {
      val newVal = i >= 0
      for (b <- bitMap.getOrElse(Math.abs(i), List()))
        bitArray(b) = newVal
    }

    def bitToInt2(bits : Seq[Int]) = {
      var curMul = 1
      var curVal = 0
      for (b <- bits) {
        if (bitArray(b))
          curVal += curMul
        curMul *= 2
      }
      curVal
    }

    (for (t <- assignments.keys) yield t -> bitToInt2(resultMap(t))).toMap
  }

  // def verifySolution(
  //   terms : Seq[Int],
  //   assignment : Map[Int,Int],
  //   eqs : Seq[Eq],
  //   goal : Goal)
  //     : Boolean = {

  //   val uf = Util.BreunionFind(terms, eqs, assignment.toList)

  //   var satisfiable = false

  //   for (subGoal <- goal.subGoals) {
  //     var subGoalSat = true

  //     var allPairsTrue = true
  //     for ((s,t) <- subGoal) {
  //       if (uf(s) != uf(t)) {
  //         allPairsTrue = false
  //       }

  //       if (!allPairsTrue)
  //         subGoalSat = false
  //     }
  //     if (subGoalSat) {
  //       satisfiable = true
  //     }
  //   }
  //   satisfiable
  // }

  def bitToInt(bits : Seq[Int]) : Int = {
    var curMul = 1
    var curVal = 0
    for (b <- bits) {
      if (solver.model contains b)
        curVal += curMul
      curMul *= 2
    }
    curVal
  }

  def termAssIntAux(i : Int, bits : Int) = {
    var curVal = i

    for (b <- 0 until bits) yield {
      if (curVal % 2 == 1) {
        curVal -= 1
        curVal /= 2
        ONEBIT
      } else {
        curVal /= 2
        ZEROBIT
      }
    }
  }

  def termEqIntAux(bitList : Seq[Int], i : Int) : Int = {
    var curVal = i

    val lits =
      (for (b <- bitList) yield {
        if (curVal % 2 == 1) {
          curVal -= 1
          curVal /= 2
          b
        } else {
          curVal /= 2
          -b
        }
      }).toArray

    val eqBit = alloc.alloc(1)
    gt.and(eqBit, new VecInt(lits))
    eqBit
  }

  def termEqTermAux(term1Bits : Seq[Int], term2Bits : Seq[Int]) : Int = {
    val maxBits = term1Bits.length max term2Bits.length

    val term1BitsPadded = term1Bits.padTo(maxBits, ZEROBIT)
    val term2BitsPadded = term2Bits.padTo(maxBits, ZEROBIT)

    // TODO: Could be optimised (by not doing padding...)
    val eqBits =
      (for ((t1b, t2b) <- term1BitsPadded zip term2BitsPadded) yield {
        // TODO: reply by match?
        if (t1b == ZEROBIT && t2b == ZEROBIT || t1b == ONEBIT && t2b == ONEBIT) {
          ONEBIT
        } else if (t1b == ZEROBIT && t2b == ONEBIT || t1b == ONEBIT && t2b == ZEROBIT) {
          return ZEROBIT
        } else {
          var tmpBit = alloc.alloc(1)
          gt.iff(tmpBit, new VecInt(Array(t1b, t2b)))
          tmpBit
        }
      }).toArray

    var eqBit = alloc.alloc(1)
    gt.and(eqBit, new VecInt(eqBits))
    eqBit
  }

  def createAssignments(problem : Problem) : Map[Int, Seq[Int]] = {
    // Connects each term with its list of bits
    // (e.g. assignment(a) = List(3,4,5))
    val terms = problem.terms

    var assignments = Map() : Map[Int, Seq[Int]]
    assignments =
      (for (t <- terms) yield {
        (t,
          (if (problem.domains(t).size == 1) {
            termAssIntAux(problem.domains(t).toList(0), problem.bits)
          } else {
            val termStartBit = alloc.alloc(problem.bits)
            val termBits = List.tabulate(problem.bits)(x => x + termStartBit)
            val assBits =
              (for (tt <- problem.domains(t); if tt <= t) yield  {
                termEqIntAux(termBits, tt)
              }).toArray
            solver.addClause(new VecInt(assBits))
            termBits}))}).toMap

    // Enforce idempotency
    for (t <- terms) {
      for (tt <- problem.domains(t); if tt <= t) {
        // Either tt = tt or t != tt
        val iddBit = termEqIntAux(assignments(tt), tt)
        val neqBit = -termEqIntAux(assignments(t), tt)
        solver.addClause(new VecInt(Array(iddBit, neqBit)))
      }
    }
    assignments
  }

  def reorderProblems(terms : Seq[Seq[Int]], domains : Seq[Domains],
    eqs : Seq[Seq[Eq]], goals : Seq[Goal]) : Seq[Int] = {
    val count = goals.length

    // 
    // Order by goals length (Increasing)
    //
    // val order  =
    //   (for (i <- 0 until count) yield
    //     (i, goals(i).length)).sortBy(_._2).map(_._1)

    // 
    // Order by goals length (Decreasing)
    //
    // BEST SO FAR?
    //

    val order  =
      (for (i <- 0 until count) yield
        (i, goals(i).subGoals.length)).sortBy(_._2).map(_._1).reverse

    //
    // Order by equation count (Increasing)
    //
    // val order = 
    //   (for (i <- 0 until count) yield
    //     (i, eqs(i).length)).sortBy(_._2).map(_._1).reverse

    //
    // Order by total domain size (Increasing)
    //
    // val order = 
    //   (for (i <- 0 until count) yield
    //     (i, ((for ((t, d) <- domains(i)) yield d.size).sum))).sortBy(_._2).map(_._1)

    //
    // Order by term count (Increasing)
    //
    // val order = 
    //   (for (i <- 0 until count) yield
    //     (i, terms(i).length)).sortBy(_._2).map(_._1)


    order
  }

  def createDQ(terms : Seq[Int],
    domains : Domains,
    eqs : Seq[Eq]) = {

    val size = if (terms.isEmpty) 0 else (terms.max + 1)
    // Store all disequalities that always must hold!

    val DQ = new Disequalities(size, eqs.toArray, checkTO)
    for (t <- terms) {
      val domain = domains(t)

      for (d <- domain) {
        DQ.cascadeRemove(t, d)
      }

      for (tt <- terms; if t != tt) {
        val ttDomain = domains(tt)
        if (domain exists ttDomain) {
          DQ.cascadeRemove(t, tt)
        }
      }
   }

    DQ
  }

  def createBaseDQ(
    terms : Seq[Int],
    domains : Domains,
    eqs : Seq[Eq]) = {
    val size = if (terms.isEmpty) 0 else (terms.max + 1)
    // Store all disequalities that always must hold!

    val baseDQ = new Disequalities(size, eqs.toArray, checkTO)
    for (t <- terms) {
      val domain = domains(t)

      for (d <- domain) {
        baseDQ.remove(t, d)
      }

      for (tt <- terms; if t != tt) {
        val ttDomain = domains(tt)
        if (domain exists ttDomain)
          baseDQ.remove(t, tt)
      }
    }

    baseDQ
  }

  private def extractTerms(domains : Map[Term, Set[Term]],
    eqs : Seq[TermEq],
    goals : Seq[Seq[(Term,Term)]]) = {

    val termSet = MSet() : MSet[Term]
    for ((_, d) <- domains)
      for (t <- d)
        termSet += t
    for ((s,t) <- goals.flatten) {
      termSet += s
      termSet += t
    }
    for ((_, args, r) <- eqs) {
      for (t <- args)
        termSet += t
      termSet += r
    }
    
    termSet.toSet
  }

  private def createTermMapping(
    terms : Seq[Term],
    domains : Map[Term, Set[Term]])
      : (Map[Term, Int], Map[Int, Term]) = {
    // Convert to Int representation
    val termToInt = MMap() : MMap[Term, Int]
    val intToTerm = MMap() : MMap[Int, Term]
    var assigned = 0

    while (assigned < terms.length) {
      for (t <- terms) {
        if (!(termToInt contains t)) {
          // Assign term after its domain is assigned (well-ordering)
          val d = domains.getOrElse(t, Set()).filter(_ != t)
          val dass = d.map(termToInt contains _)
          if (dass.forall(_ == true)) {
            termToInt += (t -> assigned)
            intToTerm += (assigned -> t)
            assigned += 1
          }
        }
      }
    }

    (termToInt.toMap, intToTerm.toMap)
  }


  private def createFunMapping(
    eqs : Seq[Seq[TermEq]]
  ) : Map[Fun, Int] = {
    var assigned = 0
    var funMap = Map() : Map[Fun, Int]
    for ((f, _, _) <- eqs.flatten) {
      if (!(funMap contains f)) {
        funMap += (f -> assigned)
        assigned += 1
      }
    }
    funMap
  }

  // Create a problem from internal (Integer) representation
  def intCreateProblem(
    domains : Domains,
    subProblems : Seq[(Goal, Seq[Eq])],
    intPosBlockingClauses : Seq[Seq[(Int, Int)]],
    intNegBlockingClauses : Seq[Seq[(Int, Int)]]) : Problem = {

    val problemCount = subProblems.length
    val allTerms = (domains.terms ++ subProblems.map{
      case (goal, eqs) => goal.terms ++ eqs.map(_.terms).flatten
    }.flatten).toList
    val bits = Util.binlog(allTerms.length)
    val arr = Array.ofDim[Int](allTerms.length, allTerms.length)

    val ffs =
      (for (p <- 0 until problemCount) yield {
        val (goals, eqs) = subProblems(p)
        // Filter terms per table
        def isUsed(term : Int, funs : Seq[Eq], goals : Goal) : Boolean = {
          goals.contains(term) || funs.exists(_.contains(term))
        }

        val ff = eqs
        val tmpFt = ListBuffer() : ListBuffer[Int]
        for (t <- (allTerms.filter(x => isUsed(x, ff, goals))))
          tmpFt += t

        // We have to add all terms that are in the domains of ft
        var ftChanged = true
        while (ftChanged) {
          ftChanged = false
          for (t <- tmpFt) {
            for (tt <- domains(t)) {
              if (!(tmpFt contains tt)) {
                tmpFt += tt
                ftChanged = true
              }
            }
          }
        }

        val ft = tmpFt

        val fd =
          Domains((for ((t, d) <- domains.domains; if (ft contains t)) yield {
            (t, d.filter(x => ft contains x))
          }).toMap)
        val fg = goals
        (ff, ft, fd, fg)
      }) : Seq[(Seq[Eq], Seq[Int], Domains, Goal)]

    val filterTerms = for ((_, ft, _, _) <- ffs) yield ft
    val filterDomains = for ((_, _, fd, _) <- ffs) yield fd
    val filterEqs = for ((ff, _, _, _) <- ffs) yield ff
    val filterGoals = for ((_, _, _, fg) <- ffs) yield fg

    val DQ =
      for (p <- 0 until problemCount)
      yield createDQ(
        filterTerms(p),
        filterDomains(p),
        filterEqs(p))

    val baseDQ =
      for (p <- 0 until problemCount)
      yield createBaseDQ(
        filterTerms(p),
        filterDomains(p),
        filterEqs(p))

    val order = reorderProblems(filterTerms, filterDomains, filterEqs, filterGoals)

    val reorderTerms = (for (i <- order) yield filterTerms(i))
    // val reorderDomains = (for (i <- order) yield filterDomains(i))
    val reorderGoals = (for (i <- order) yield filterGoals(i))
    val reorderEqs =
      (for (i <- order) yield filterEqs(i))
    val reorderDQ = (for (i <- order) yield DQ(i))
    val reorderBaseDQ = (for (i <- order) yield baseDQ(i))


    val problems =
      for (i <- 0 until problemCount) yield
        new SubProblem(reorderTerms(i)
          reorderEqs(i), reorderGoals(i),
          reorderDQ(i), reorderBaseDQ(i))

    new Problem(
      allTerms,
      domains,
      bits,
      order,
      problems,
      intPosBlockingClauses,
      intNegBlockingClauses)
  }


  // TODO: No timeouts for creating problems
  def createProblem(
    domains : TermDomains,
    goals : Seq[TermGoal],
    eqs : Seq[Seq[TermEq]],
    posBlockingClauses : Seq[Seq[(Term, Term)]],
    negBlockingClauses : Seq[Seq[(Term, Term)]]) : Instance[Term, Fun] = {

    curId += 1
    val problemCount = goals.length
    val pairs = for (i <- 0 until problemCount) yield { (goals(i), eqs(i)) }

    //
    // Convert to Int representation
    //

    // TODO: Maybe check that terms in eqs and goals actually have domains?
    val termSets = 
      for (p <- 0 until problemCount) yield
        extractTerms(domains, eqs(p), goals(p))

    val allTerms = (termSets.:\(Set() : Set[Term])(_ ++ _)).toList
    val terms = for (p <- 0 until problemCount) yield allTerms
    val bits = Util.binlog(allTerms.length)


    val (termToInt, intToTerm) = createTermMapping(allTerms, domains)
    val funMap = createFunMapping(eqs)
    val intAllTerms = allTerms.map(termToInt)

    // TODO: Maybe add option for this?: Each term is added to its own domain
    // TODO: http://stackoverflow.com/questions/1715681/scala-2-8-breakout/1716558#1716558
    val newDomains = 
      Domains((for (t <- allTerms) yield {
        val oldDomain = domains.getOrElse(t, Set(t))
        (termToInt(t) -> oldDomain.map(termToInt))
      }).toMap)


    // 
    // Convert each subproblem
    // + to integer representation

    // Conversion might introduce new terms, nextTerm shows next available term
    // Increasing by one allocates one new term (which is added to domain, etc.)
    var nextTerm = if (intAllTerms.length > 0) intAllTerms.max + 1 else 0

    val subProblems = 
      for ((goals, funs) <- pairs) yield {


        val extraEqs = ListBuffer() : ListBuffer[Eq]
        val extraSubGoals = ListBuffer() : ListBuffer[Seq[(Int, Int)]]

        val newGoal  = Goal((for (pairs <- goals) yield for ((s, t) <- pairs) yield (termToInt(s), termToInt(t))) ++ extraSubGoals)
        val newEqs = (for ((f, args, r) <- funs) yield Eq(funMap(f), args.map(termToInt), termToInt(r))) ++ extraEqs

        (newGoal, newEqs : Seq[Eq])
      }



    val intPosBlockingClauses = ListBuffer() : ListBuffer[List[(Int, Int)]]

    for (bc <- posBlockingClauses) {
      if (bc.forall{ case (s,t) => (terms contains s) && (terms contains t)})
        intPosBlockingClauses += bc.map{ case (s,t) => (termToInt(s), termToInt(t)) }.toList
    }


    val intNegBlockingClauses = ListBuffer() : ListBuffer[List[(Int, Int)]]

    for (bc <- negBlockingClauses) {
      if (bc.forall{ case (s,t) => (terms contains s) && (terms contains t)})
        intNegBlockingClauses += bc.map{ case (s,t) => (termToInt(s), termToInt(t)) }.toList
    }    

    val problem = intCreateProblem(newDomains, subProblems, intPosBlockingClauses.toList, intNegBlockingClauses.toList)

    new Instance[Term, Fun](curId, this, problem, termToInt.toMap, domains)
  }

  def createProblem(
    domains : TermDomains,
    goals : Seq[TermGoal],
    eqs : Seq[Seq[TermEq]]) : Instance[Term, Fun] = createProblem(domains, goals, eqs, List(), List())
}

