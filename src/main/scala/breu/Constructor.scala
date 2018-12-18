package breu;

import scala.collection.mutable.ListBuffer

/*
 * Helper class for constructing BREU-problems
 * 
 * New restriction: Can only add sub-problems, never go back and edit earlier ones
 */

class Constructor[Term, Fun](debug : Boolean = false) {

  // Some useful types
  type Domain = (Term, Set[Term])
  type FunApp = (Fun, Seq[Term], Term)
  type Goal = Seq[(Term, Term)]

  // Subproblems are stored here
  // TODO: Maybe replace by just storing last one and storing subProblems
  val domains : ListBuffer[Domain] = ListBuffer()
  val eqs : ListBuffer[ListBuffer[FunApp]] = ListBuffer()
  val goals : ListBuffer[ListBuffer[Goal]] = ListBuffer()


  // State
  var subProblems = 0
  var instance = None : Option[Instance[Term, Fun]]

  // Auxilliary information from solvers
  var tableColumns = List() : List[Int]
  var posBlockingClauses = List() : List[List[(Term, Term)]]
  var negBlockingClauses = List() : List[List[(Term, Term)]]  
  // var unitClauses = List() : List[(Int, Int)]
  var model = None : Option[Map[Term,Term]]

  def addDomain(t : Term, d : Set[Term]) =
    domains += ((t, d))

  def newSubproblem() = {
    subProblems += 1
    eqs += ListBuffer()
    goals += ListBuffer()
  }

  def addFunction(f : FunApp) =
    eqs(subProblems-1) += f

  def addGoal(g : Goal) =
    goals(subProblems-1) += g

  override def toString() : String = {
    " CONSTRUCTOR\n" +
    "Subproblems: " + subProblems + "\n" +
    "Domains:\n" +
    (for ((t, d) <- domains) yield {
      "\t" + t + " -> " + d.mkString(",")
    }).mkString("\n") + "\n" + 
    (for ((fs, gs) <- eqs zip goals) yield {
      "< --- SUBPROBLEM --- >\n" +
      "Eqs:\n" +
      (for ((f, args, r) <- fs) yield ("\t" + f + "(" + args.mkString(",") + ") = " + r)).mkString("\n") + "\n" +
      "Goals:\n" +
      (for (g <- gs) yield ("\t" + g)).mkString("\n")
    }).mkString("\n")
  }

  private def solve(solver : breu.Solver[Term,Fun], timeout : Long, posBlockingClauses_ : List[List[(Term, Term)]], negBlockingClauses_ : List[List[(Term, Term)]]) = {
    // Create Problem
    val prob = solver.createProblem(
      domains.toMap,
      goals.toList,
      eqs.toList,
      posBlockingClauses_,
      negBlockingClauses_      
    )
    instance = Some(prob)


    // Solve Problem
    val res = prob.solve(timeout)

    val tm = termMap()
    model = 
      if (prob.model.isDefined) {
        Some((for ((k, v) <- prob.model.get) yield {
          (tm(k), tm(v))
        }).toMap)
      } else {
        None
      }

    res
  }

  def solveTable(timeout : Long) = {
    val solver = new breu.TableSolver[Term,Fun](debug)
    val ret = solve(solver, timeout, List(), List())
    if (debug) {
      tableColumns = 
        (for (t <- solver.tables) yield {
          if (t.isDefined)
            t.get.currentColumn + 1
          else
            0
        }).toList
    }
    ret
  }

  def solveLazy(timeout : Long, posBlockingClauses_ : List[List[(Term, Term)]] = List(), negBlockingClauses_ : List[List[(Term, Term)]] = List()) = {
    val solver = new breu.LazySolver[Term,Fun](debug)
    val ret = solve(solver, timeout, posBlockingClauses_, negBlockingClauses_)

    val tm = termMap()
    posBlockingClauses = 
      (for (bc <- solver.positiveBlockingClauses) yield {
        (for ((s, t) <- bc) yield {
          (tm(s), tm(t))
        }).toList
      }).toList

    negBlockingClauses = 
      (for (bc <- solver.negativeBlockingClauses) yield {
        (for ((s, t) <- bc) yield {
          (tm(s), tm(t))
        }).toList
      }).toList    

    ret
  }

  // TODO: Maybe place this in Instance
  def termMap() : Map[Int, Term] = {
    if (!instance.isDefined)
      throw new Exception("Trying to get termMap with no problem")
    else
      (instance.get.termMap).map(_.swap)
  }
}
