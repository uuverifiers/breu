//TODO: Add unit clauses

// TODO : Proposal, use s, t for terms and ss,tt for integer representations

package breu

import scala.collection.mutable.{ListBuffer, Map => MMap}
import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.{ISolver, IConstr}
import org.sat4j.core.VecInt

/**
  * Three different result types
  * UKNOWN generally indicates an error or timeout
  */
object Result extends Enumeration {
  type Result = Value
  val SAT, UNSAT, UNKNOWN = Value
}

class TimeoutException(msg : String) extends Exception("TimeoutException: " + msg)

//
// The new BREU solver.
//
// Uses the lazy approach
//
// Add terms, eqs and goals, then use push() to save subproblem.
// Pop to remove latest subproblem (including terms)
//
class Solver[Term, Fun] {

  var DEBUG = false

  val DEFAULT_TIMEOUT = 5

  // TODO: This is set upon object creation, perhaps better as argument?
  var START_TIME : Long = System.currentTimeMillis
  var MAX_TIME : Long = 0


  val CONSTRAINTS = ListBuffer() : ListBuffer[(IConstr, String)] 
  val solver = SolverFactory.newDefault()
  solver.newVar(1000000);
  solver.setTimeout(1)

  // TODO: BITS SHOULD BE DYNAMIC...
  val BITS = 8
  val maxVars = Math.pow(2, BITS).toInt

  // SPECIAL CASE, teqt(s,s) is constraint s.t. s == termToInt(s)
  val TEQT = Array.fill[Int](maxVars, maxVars)(-1)


  val gt = new GateTranslator(solver)

  def terms() = domains.keys.toList
  def allTerms() = domains.keys.toList.map(termToInt(_))
  def intDomains() = domains.map{case (k, v) => termToInt(k) -> v.map(termToInt(_))}
  def termMap() = termToInt.map(_.swap)
  def size() = subProblems.length

  // Bit manipulation
  val alloc = new Allocator
  val ZEROBIT = 1
  val ONEBIT = 2

  resetSat4j()  


  // Some useful types
  type Domain = MMap[Term, Set[Term]]
  type FunApp = (Fun, Seq[Term], Term)
  type Goal = Seq[(Term, Term)]
  type UnificationConstraint = List[(Term, Term)]
  type DisunificationConstraint = List[(Term, Term)]

  val domains : Domain = MMap()
  val assignments :  MMap[Int, Seq[Int]] = MMap()

  val curEqs : ListBuffer[FunApp] = ListBuffer()
  val curGoals : ListBuffer[Goal] = ListBuffer()
  val curTerms : ListBuffer[Term] = ListBuffer()

  // Tracking the TermMap
  var nextTermInt = 0
  val termToInt = MMap() : MMap[Term, Int]

  var nextFunInt = 0
  val funToInt = MMap() : MMap[Fun, Int]  

  var subProblems = List() : List[SubProblem]

  var constraintStack = List() : List[List[IConstr]]
  var curConstraints = List() : List[IConstr]
  var termStack = List() : List[List[Term]]
  var unificationConstraintsStack = List() : List[List[UnificationConstraint]]
  var disunificationConstraintsStack = List() : List[List[DisunificationConstraint]]

  var curUnificationConstraints = List() : List[UnificationConstraint]
  var curDisunificationConstraints = List() : List[DisunificationConstraint]

  var nextDummyPredicate = 0
  var level = 0

  def genDummyPredicate() : String = {
    nextDummyPredicate += 1
    val newPred = "dummy_predicate_" + nextDummyPredicate
    newPred
  }

  def restart() = {
    resetSat4j()
    subProblems = List()
    domains.clear
    curTerms.clear
    termToInt.clear
    funToInt.clear
    nextTermInt = 0
    nextFunInt = 0
    termStack = List()
    unificationConstraintsStack = List()
    disunificationConstraintsStack = List()
  }


  def resetSat4j() = {
    solver.reset()
    alloc.reset
    val constr1 = solver.addClause(new VecInt(Array(-ZEROBIT)))
    CONSTRAINTS += ((constr1 , "ZEROBIT"))
    val constr2 = solver.addClause(new VecInt(Array(ONEBIT)))
    CONSTRAINTS += ((constr2, "ONEBIT"))
  }


  override def toString() = {
    val tm = termToInt.map{case (t, i) => (i, t.toString)}.toMap
    "<<<< BREU PROBLEM >>>\n" + 
    "  DOMAINS\n" +
    domains.mkString("\n") + "\n\n" +
    subProblems.map(_.toTermString(tm)).mkString("\n") + "\n" +
    (if (unificationConstraintsStack.flatten.length + disunificationConstraintsStack.flatten.length > 0) {
      "  BLOCKING CONSTRAINTS \n" +
      " POSITIVE \n" +
      unificationConstraintsStack.mkString("...") + "\n" +
      " NEGATIVE \n " +
      disunificationConstraintsStack.mkString("...")
    } else {""})

  }

  def internal() = {
    println("<<< INTERNAL BREU PROBLEM >>>")
    for (t <- terms().sortBy(termToInt))
      println("\t" + t + " (" + termToInt(t) + ") [" + assignments(termToInt(t)).mkString(",") + "]: ")
    println("<<< CONSTRAINTS >>>")
    for ((c, str) <- CONSTRAINTS; if (c != null))
      println("\t" + c + " ==> " +  str)

    println("<<< TEQT >>>")
    for (row <- TEQT) {
      println(row.mkString(", "))
    }
  }

  def toIntString() = {
    "<<<< BREU PROBLEM >>>\n" + 
    "  DOMAINS\n" +
    domains.map{case (t, d) => termToInt(t) + ":\t" + d.map(termToInt(_)).mkString(", ")}.mkString("\n") + "\n" +
    subProblems.mkString("\n") + "\n"     
  }

  def checkTO() = {
    if (MAX_TIME > 0 && MAX_TIME < System.currentTimeMillis - START_TIME)
      throw new TimeoutException("BREU")
  }  


  def satSolve() : Boolean = {
    checkTO()
    if (MAX_TIME > 0) {
      val REM_TIME = MAX_TIME - (System.currentTimeMillis - START_TIME)
      solver.setTimeoutMs(REM_TIME)
    } else {
      solver.setTimeout(5)
      // TODO: throw new Exception("No timeout for sat solver...")
    }
    try {
      solver.isSatisfiable()
    } catch {
      case te : org.sat4j.specs.TimeoutException => {
        throw new TimeoutException("sat4j")
      }
    }
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

  // Problem creation functions
  def addVariable(t : Term, d : Set[Term]) = {
    if (domains.size >= Math.pow(2, BITS).toInt)
      throw new Exception("Too many terms")
    if (domains contains t)
      throw new Exception("Trying to add existing term!")

    // Check that all terms in domain are added
    val missingTerm = (d - t).find(t => !(domains contains t))
    if (missingTerm.isDefined)
      throw new Exception("Term " +  missingTerm.get + " is not added yet.")

    // Add new term to all structures
    val tt = nextTermInt
    nextTermInt += 1
    curTerms.prepend(t)
    termToInt += t -> tt
    domains += ((t, d))


    if (d.size == 1) {
      assignments += tt -> termAssIntAux(tt)
    } else {
      val termStartBit = alloc.alloc(BITS)
      val termBits = List.tabulate(BITS)(x => x + termStartBit)
      assignments += tt -> termBits

      val assBits =
        (for (s <- d; if termToInt(s) <= tt) yield  {
          // Enforce idempotency
          // Either s = t or t != s
          val ss = termToInt(s)
          val iddBit = teqt(ss, ss)
          val neqBit = -termEqIntAux(termBits, ss)
          val constr = solver.addClause(new VecInt(Array(iddBit, neqBit)))
          CONSTRAINTS += ((constr, ("IDEMPOTENCY of " + t + " and " + s)))
          curConstraints = constr :: curConstraints

          termEqIntAux(termBits, ss)
        }).toArray
      val constr = solver.addClause(new VecInt(assBits))
      CONSTRAINTS += ((constr, "DOMAIN of " + t))
      curConstraints = constr :: curConstraints
    }
  }

  // TODO: addConstants? with repeated arguments...
  def addConstant(c : Term) = addVariable(c, Set(c))
  def addConstants(cs : Term*) = for (c <-cs) addConstant(c)

  def addFunction(f : FunApp) = {
    if (!(funToInt contains f._1)) {
      funToInt += f._1 -> nextFunInt
      nextFunInt += 1
    }

    curEqs += f
  }

  def addGoal(g : Goal) =
    curGoals += g

  def addUnificationConstraint(constr : List[(Term, Term)]) = {
    curUnificationConstraints = constr :: curUnificationConstraints 
  }

  def addDisunificationConstraint(constr : List[(Term, Term)]) = {
    curDisunificationConstraints = constr :: curDisunificationConstraints 
  }  


  def push(timeout : Long = 0) = {
    if (DEBUG)
      println("PUSH(" + level + ")")
    MAX_TIME = timeout
    level += 1
    val breuTerms = domains.keys.toList.map(termToInt(_))
    val breuDomains = breu.Domains((domains.map{case (k, v) => termToInt(k) -> v.map(termToInt(_))}).toMap)
    val breuEqs : List[breu.Eq] = curEqs.map{case (f, a, r) => breu.Eq(funToInt(f), a.map(termToInt(_)), termToInt(r))}.toList
    val breuGoals : breu.Goal = Goal(curGoals.map{x => x.map{ case (s,t) => (termToInt(s), termToInt(t)) }})
    val dq =
      createDQ(
        breuTerms,
        breuDomains,
        breuEqs)

    val baseDQ =
      createBaseDQ(
        breuTerms,
        breuDomains,
        breuEqs)

    val newSubProblem =
      SubProblem(
        breuTerms,
        breuEqs,
        breuGoals,
        dq,
        baseDQ)

    subProblems = newSubProblem :: subProblems
    termStack = curTerms.toList :: termStack
    constraintStack = curConstraints :: constraintStack
    
    unificationConstraintsStack = curUnificationConstraints :: unificationConstraintsStack
    disunificationConstraintsStack = curDisunificationConstraints :: disunificationConstraintsStack    

    curEqs.clear()
    curGoals.clear()
    curTerms.clear()
    curConstraints = List()
    curUnificationConstraints = List()
    curDisunificationConstraints = List()
  }

  def pop() = {
    if (DEBUG)
    println("POP(" + level + ")")
    level -= 1
    // TODO: Add assert making sure there are no current added stuff (not pushed)
    subProblems = subProblems.tail

    // Removing all traces of term t
    for (t <- termStack.head) {
      val remTerm = termToInt(t)
      for (i <- 0 until TEQT.length) {
        // TODO: This could be reduced to upper triangle..
        TEQT(i)(remTerm) = -1
        TEQT(remTerm)(i) = -1
      }
      nextTermInt -= 1
      assert(termToInt(t) == nextTermInt)

      assignments -= remTerm
      domains -= t      
      termToInt -= t
    }
    termStack = termStack.tail

    for (c <- constraintStack.head) {
      if (c != null) {
        solver.removeConstr(c)
        CONSTRAINTS -= CONSTRAINTS.find(_._1 == c).get
      } 
    }
    constraintStack = constraintStack.tail
    unificationConstraintsStack = unificationConstraintsStack.tail
    disunificationConstraintsStack = disunificationConstraintsStack.tail
  }

  def clear() : Unit = {
    if (!subProblems.isEmpty) {
      pop()
      clear()
    }
  }


  // State
  // var subProblems = 0

  // Auxilliary information from solvers
  // var posBlockingClauses = List() : List[List[(Term, Term)]]
  // var negBlockingClauses = List() : List[List[(Term, Term)]]  
  var model = None : Option[Map[Int,Int]]

  // Solve the  problem by:
  // (1) Generate a random assignments A
  // (2) Check if A is a solution to the problem
  // (2a) if NO, go to (3)
  // (2b) if YES, terminate with A
  // (3) Generate blocking clause B that excludes A
  // (4) Add B to the constraints and generate new assignment A'
  // (5) Let A = A' and go to (2)
  def solve(timeout : Long = 0) : breu.Result.Result =
    Timer.measure("LazySolver.solveaux") {
      MAX_TIME = timeout

      // Used to store what bits are equivalent to term equal term
      // If we do not have dense terms we have to take max instead of length?


      // Keeps track whether a subproblem has triggered UNSAT
      val blockingProblem = Array.ofDim[Boolean](subProblems.length)

      def handleBlockingProblem(cp : SubProblem, solution : Map[Int, Int]) =
        Timer.measure("handleBlockingProblem") {
          // val DQ = new Disequalities(cp.DQ)
          val DQ = new Disequalities(cp.terms.max+1, cp.funEqs.toArray, checkTO)

          // Could we replace this by just doing cascade-remove on the assignments?
          val uf = Util.BreunionFind(cp.terms, List(), solution.toList)

          // TODO: Can we change this to if (s < t) ...
          for (s <- cp.terms; t <- cp.terms;
            if (s <= t); if (uf(s) == uf(t))) {
            DQ.cascadeRemove(s, t)
          }

          def heuristic(dq : (Int, Int)) = {
            val (s, t) = dq
            // intDomains()(s).size
            0
          }

          // Now we minimize DI to only contain "relevant" inequalities
          DQ.minimise(cp.terms, cp.goal.subGoals, heuristic)


          // Remove all "base" inequalities, since they will always be there
          val ineqs = DQ.inequalities(cp.terms)
          val finalDQ = for ((s,t) <- ineqs; if cp.baseDQ(s, t)) yield (s, t)

          assert(!DQ.satisfies(cp.goal.subGoals), "Minimization failed")

          // TODO: Maybe we can do this more efficient
          val blockingClause =
            (for ((s,t) <- finalDQ) yield {
              teqt(s, t)
            }).toArray

          if (finalDQ.length == 1) {
            val (s,t) = finalDQ(0)
            // unitClauses += ((s,t))
          }

          try {
            // positiveBlockingClauses += finalDQ.toList            
            val constr = solver.addClause(new VecInt(blockingClause))
            CONSTRAINTS += ((constr, "BLOCKING CLAUSE: " + finalDQ.mkString(" v ")))
            curConstraints = constr :: curConstraints
            // bcCount += 1
            false
          } catch {
            case e : org.sat4j.specs.ContradictionException => {
              true
            }
          }
        }

      // If all problems are SAT or one problem is infeasible, we are done
      var allSat = false
      var infeasible = false
      var candidate = Map() : Map[Int, Int]

      // Check the "hardest" problem first!
      var problemOrder = List.tabulate(size())(x => x)


      // Add given blocking clauses
      for (uc <- unificationConstraintsStack.flatten) {
        val blockingClause =
          (for ((ss,tt) <- uc) yield {
            val (s,t) = (termToInt(ss), termToInt(tt))
            teqt(s, t)
          }).toArray

        try {
          // positiveBlockingClauses += bc.toList
          val constr = solver.addClause(new VecInt(blockingClause))
          CONSTRAINTS += ((constr, "GIVEN BLOCKING CLAUSE: " + uc.mkString(" v ")))
          curConstraints = constr :: curConstraints
          // bcCount += 1
        } catch {
          case e : org.sat4j.specs.ContradictionException => {
            throw new Exception("Blocking Clauses are Contradictory")
          }
        }
      }

      for (dc <- disunificationConstraintsStack.flatten) {
        val blockingClause =
          (for ((ss,tt) <- dc) yield {
            val (s,t) = (termToInt(ss), termToInt(tt))
            -teqt(s, t)
          }).toArray

        try {
          // negativeBlockingClauses += bc.toList
          val constr = solver.addClause(new VecInt(blockingClause))
          CONSTRAINTS += ((constr, "GIVEN (NEG) BLOCKING CLAUSE: " + dc.mkString(" ... ")))          
          curConstraints = constr :: curConstraints
          // bcCount += 1
        } catch {
          case e : org.sat4j.specs.ContradictionException => {
            throw e
            // throw new Exception("Blocking Clauses are Contradictory")
          }
        }
      }      

      var iterations = 0
      // (1) Generate a random assignments A
      while (!infeasible && !allSat && satSolve()) {
        iterations += 1
        checkTO()
        Timer.measure("LazySolver.assignmentsToSolution)") {
          candidate = assignmentsToSolution(assignments.toMap)
        }

        
        // (2) Check if A is a solution to the problem
        testSolution(candidate) match {
          // (2a) if NO, go to (3)
          case Some(p) => {
            blockingProblem(p) = true
            // (3) Generate blocking clause B that excludes A
            // (4) Add B to the constraints and generate new assignment A'
            // (5) Let A = A' and go to (2)
            if (handleBlockingProblem(subProblems(p), candidate)) {
              infeasible = true
            }
            problemOrder = p::problemOrder.filter(_ != p)
          }

          // (2b) if YES, terminate with A
          case None => allSat = true
        }
      }


      if (allSat) {
        model = Some(candidate)
        breu.Result.SAT
      } else {
        // lastUnsatCore =
        //   (for (i <- 0 until size(); if (blockingProblem(i))) yield i)
        breu.Result.UNSAT
      }
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

  // Converts an integer to a bit representation using "bits" bits
  def termAssIntAux(i : Int) = {
    var curVal = i

    for (b <- 0 until BITS) yield {
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


  // Makes a bit eqBit <=> int(bitList) = i
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

  def teqt(s : Int, t : Int) : Int = {
    if (TEQT(s min t)(s max t) == -1) {
      TEQT(s min t)(s max t) =
        if (s == t)
          termEqIntAux(assignments(s), s)
        else
          termEqTermAux(assignments(s), assignments(t))
    }
    TEQT(s min t)(s max t)
  }


  // def createAssignments() : Map[Int, Seq[Int]] = {
  //   // Connects each term with its list of bits
  //   // (e.g. assignment(a) = List(3,4,5))
  //   val terms = allTerms()
  //   val idomains = intDomains()

  //   var assignments = Map() : Map[Int, Seq[Int]]
  //   assignments =
  //     (for (t <- terms) yield {
  //       (t,
  //         (if (idomains(t).size == 1) {
  //           val r = termAssIntAux(idomains(t).toList(0))
  //           r
  //         } else {
  //           val termStartBit = alloc.alloc(BITS)
  //           val termBits = List.tabulate(BITS)(x => x + termStartBit)
  //           val assBits =
  //             (for (tt <- idomains(t); if tt <= t) yield  {
  //               termEqIntAux(termBits, tt)
  //             }).toArray
  //           val constr = solver.addClause(new VecInt(assBits))
  //           CONSTRAINTS += ((constr, " " + finalDQ.mkString(" v ")))
  //           curConstraints = constr :: curConstraints
  //           termBits}))}).toMap

  //   // Enforce idempotency
  //   for (t <- terms) {
  //     for (tt <- idomains(t); if tt <= t) {
  //       // Either tt = tt or t != tt
  //       val iddBit = termEqIntAux(assignments(tt), tt)
  //       val neqBit = -termEqIntAux(assignments(t), tt)
  //       val constr = solver.addClause(new VecInt(Array(iddBit, neqBit)))
  //       curConstraints = constr :: curConstraints
  //     }
  //   }
  //   assignments
  // }
  

  def testSolution(solution : Map [Int, Int]) = {
    val idx = subProblems.indexWhere(!_.verifySolution(solution))
    if (idx == -1) None
    else Some(idx)
  }


  //
  //
  //   Functions that returns things as terms
  //
  //

  def getAddedTerms() : Set[Term] = {
    domains.keys.toSet
  }


  def getBlockingClauses() : (List[List[(Term, Term)]], List[List[(Term, Term)]]) = {
    // val tm = termToInt.map(_.swap)
    // val posBC =
    //   (for (bc <- positiveBlockingClauses) yield {
    //     (for ((s, t) <- bc) yield {
    //       (tm(s), tm(t))
    //     }).toList
    //   }).toList

    // val negBC =
    //   (for (bc <- negativeBlockingClauses) yield {
    //     (for ((s, t) <- bc) yield {
    //       (tm(s), tm(t))
    //     }).toList
    //   }).toList

    // (posBC, negBC)
    (List(), List())
  }

  def getModel() : Map[Term, Term] = {
    val tm = termToInt.map(_.swap)

   (for ((s, t) <- model.get) yield (tm(s) -> tm(t))).toMap
  }

//   override def getStat(result : breu.Result.Result) = 
//     "LAZY>RESULT:" + result + ",BLOCKINGCLAUSES:" + bcCount

//   def unsatCoreAux(problem : Problem, timeout : Int) = lastUnsatCore

//   // def unitBlockingClauses = unitClauses
//   // def blockingClauses = savedBlockingClauses

//   // We automatically calculate unsatCore
//   var lastUnsatCore = List() : Seq[Int]
//   var unitClauses = ListBuffer() : ListBuffer[(Int, Int)]
//   var bcCount = 0
}
