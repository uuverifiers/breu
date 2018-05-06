package breu;


case class BREUGoal(val subGoals : Seq[Seq[(Int, Int)]]) {
  override def toString = subGoals.mkString(" OR ")
}

case class BREUEq(val eq : (Int, Seq[Int], Int)) {
  val fun = eq._1
  val args = eq._2
  val res = eq._3

  override def toString = fun + "(" + args.mkString(",") + ")=" + res
}

case class BREUSubProblem(
  val terms : Seq[Int],
  val domains : Map[Int, Set[Int]],
  val funEqs : Seq[BREUEq],
  val goal : BREUGoal,
  val DQ : Disequalities,
  val baseDQ : Disequalities) {

  override def toString = {
    "BREUSubProblem"
  }

  def solvable = {
    // subgoalsat(0) = true of subgoal(0) is solvable
    val subgoalsat = for (subgoal <- goal.subGoals) yield
      (for ((s, t) <- subgoal) yield DQ(s, t)).foldRight(true)(_ && _)

    subgoalsat.foldRight(false)(_ || _)
  }

  def verifySolution(solution : Map[Int, Int]) = {
    val uf = Util.BreunionFind(terms, funEqs, solution.toList)
    var satisfiable = false

    for (subGoal <- goal.subGoals) {
      var subGoalSat = true

      var allPairsTrue = true
      for ((s,t) <- subGoal) {
        if (uf(s) != uf(t)) {
          allPairsTrue = false
        }

        if (!allPairsTrue)
          subGoalSat = false
      }
      if (subGoalSat) {
        satisfiable = true
      }
    }
    satisfiable    
  }
}

case class BREUSimProblem(
  val terms : Seq[Int],
  val domains : Map[Int, Set[Int]],
  val bits : Int,
  val order : Seq[Int],
  val subProblems : Seq[BREUSubProblem]) {

  val size = subProblems.length

  override def toString  = {
    var str = ""
    str += "//-------------\n"
    for (t <- terms)
      str += "| " + t + " = {" + (domains.getOrElse(t, Set(t))).mkString(", ") + "}" + "\n"
    str += "| Size: " + size + "\n"
    str += "| Bits: " + bits + "\n"
    str += "| Order: " + order + "\n"
    for (p <- 0 until size) {
      str += "+--------\n"
      str += "| terms: " + subProblems(p).terms + "\n"
      str += "| domains: " + subProblems(p).domains + "\n"
      str += "| funEqs: " + subProblems(p).funEqs + "\n"
      str += "| goal: " + subProblems(p).goal + "\n"
      // str += "| DQ: " + subProblems(p).DQ + "\n"
      // str += "| baseDQ: " + subProblems(p).baseDQ + "\n"
      str += subProblems(p).toString + "\n"
    }
    str += "\\\\-------------\n"
    str
  }

  def saveToFile(filename : String) = {
    var str = ""
    str += "DOMAINS\n"
    for (t <- terms)
      str += t + "=" + (domains.getOrElse(t, Set(t))).mkString(",") + "\n"
    for (p <- 0 until size) {
      str += "PROBLEM\n"
      for (f <- subProblems(p).funEqs)
        str += f.fun + "(" + f.args.mkString(",") + ")=" + f.res + "\n"
      for (g <- subProblems(p).goal.subGoals)
        str += g.map(x => x._1 + "=?" + x._2).mkString("|") + "\n"
    }

    import java.io._
    new File("breu-debug/").mkdir()
    val pw = new PrintWriter(filename)
    pw.write(str)
    pw.close
  }

  def apply(i : Int) = subProblems(i)

  def solvable = subProblems.map(_.solvable).foldRight(true)(_ && _)

  // None if solution works, else Some(idx) where idx is a failing problem
  def testSolution(solution : Map [Int, Int]) = {
    val idx = subProblems.indexWhere(!_.verifySolution(solution))
    if (idx == -1) None
    else Some(idx)
  }

  // True if solution works, else false
  def verifySolution(solution : Map[Int, Int]) =
    testSolution(solution).isEmpty

}
