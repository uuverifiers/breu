package breu;


case class Goal(val subGoals : Seq[Seq[(Int, Int)]]) {
  override def toString = subGoals.mkString(" OR ")

  def stringWithTermMap(intMap : Map[Int, String]) = {
    subGoals.map(sg => sg.map{ case (s,t) => (intMap(s), intMap(t)) }).mkString(" OR ")
  }

  val terms : Set[Int] = subGoals.flatten.map(x => List(x._1, x._2)).flatten.toSet
  def contains(term : Int) : Boolean = {
    for (g <- subGoals)
      for ((s, t) <- g)
        if (s == term || t == term)
          return true
    return false
  }

}

case class Eq(val fun : Int, val args : Seq[Int], val res : Int) {
  override def toString = fun + "(" + args.mkString(",") + ")=" + res

  def stringWithTermMap(intMap : Map[Int, String]) = {
    fun + "(" + args.map(intMap(_)).mkString(",") + ")=" + intMap(res)
  }
  val terms : Set[Int] = args.toSet + res
  def contains(term : Int) : Boolean = {
    if (res == term)
      return true
    for (a <- args)
      if (a == term)
        return true
    return false
  }
}

case class Domains(val domains : Map[Int, Set[Int]]) {
  override def toString = domains.mkString("\n")
  def apply(i : Int) = {
    domains.getOrElse(i, Set(i))
  }

  val terms : Set[Int]  = (for ((_, d) <- domains) yield d).flatten.toSet
}

case class SubProblem(
  val terms : Seq[Int],
  val domains : Domains,
  val funEqs : Seq[Eq],
  val goal : Goal,
  val DQ : Disequalities,
  val baseDQ : Disequalities) {

  override def toString = {
    "SubProblem"
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

case class Problem(
  val terms : Seq[Int],
  val domains : Domains,
  val bits : Int,
  val order : Seq[Int],
  val subProblems : Seq[SubProblem],
  val positiveBlockingClauses : Seq[Seq[(Int, Int)]] = List(),
  val negativeBlockingClauses : Seq[Seq[(Int, Int)]] = List())  {

  val size = subProblems.length

  override def toString  = {
    val builder = new StringBuilder
    builder ++= "//-------------\n"
    for (t <- terms)
      builder ++= "| " + t + " = {" + (domains(t)).mkString(", ") + "}" + "\n"
    builder ++= "| Size: " + size + "\n"
    builder ++= "| Bits: " + bits + "\n"
    builder ++= "| Order: " + order + "\n"
    for (p <- 0 until size) {
      builder ++= "+--------\n"
      builder ++= "| terms: " + subProblems(p).terms + "\n"
      builder ++= "| domains: " + subProblems(p).domains + "\n"
      builder ++= "| funEqs: " + subProblems(p).funEqs + "\n"
      builder ++= "| goal: " + subProblems(p).goal + "\n"
      // builder ++= "| DQ: " + subProblems(p).DQ + "\n"
      // builder ++= "| baseDQ: " + subProblems(p).baseDQ + "\n"
      builder ++= subProblems(p).toString + "\n"
    }
    builder ++= "\\\\-------------\n"
    builder.toString
  }

  def stringWithTermMap(termMap : Map[Int, String]) : String = {
    val builder = new StringBuilder
    builder ++= "/----DOMAINS----\n"
    for (t <- terms)
      builder ++= "| " + termMap(t) + " = {" + domains(t).map(termMap(_)).toList.sorted.mkString(",") + "}" + "\n"
    builder ++= "| Size: " + size + "\n"
    builder ++= "| Bits: " + bits + "\n"
    builder ++= "| Order: " + order + "\n"
    for (p <- 0 until size) {
      builder ++= "+------(" + p + ")------\n"
      builder ++= "| funEqs: " + subProblems(p).funEqs.map(_.stringWithTermMap(termMap)) + "\n"
      builder ++= "| goal: " + subProblems(p).goal.stringWithTermMap(termMap) + "\n"
    }
    builder ++= "\\---------------\n"
    builder.toString
  }

  def saveToFile(filename : String) = {
    val builder = new StringBuilder
    builder ++= "DOMAINS\n"
    for (t <- terms)
      builder ++= t + "=" + (domains(t)).mkString(",") + "\n"
    for (p <- 0 until size) {
      builder ++= "PROBLEM\n"
      for (f <- subProblems(p).funEqs)
        builder ++= f.fun + "(" + f.args.mkString(",") + ")=" + f.res + "\n"
      for (g <- subProblems(p).goal.subGoals)
        builder ++= g.map(x => x._1 + "=?" + x._2).mkString("|") + "\n"
    }

    import java.io._
    new File("breu-debug/").mkdir()
    val pw = new PrintWriter(filename)
    pw.write(builder.toString)
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
