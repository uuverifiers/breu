package breu;

object Tester {

  def checkTO() = {
  }

  def test(file : String, timeout : Long) : breu.Result.Value = {
    val cons = new breu.Constructor[String,String]()

    val input = io.Source.fromFile(file).getLines.toList

    var section = ""

    val dPattern = "(.*)=(.*)".r
    val fPattern = "(.*)\\((.*)\\)=(.*)".r
    val gPattern = "(.*=\\?.*\\|?)+".r    

    for (l <- input) {
      l.trim() match {
        case dPattern(t,d) if section == "domains" => cons.addDomain(t, d.split(",").toSet)
        case fPattern(f,ts,t) if section == "problem" => cons.addFunction((f, ts.split(","), t))
        case gPattern(sgoals) => {
          val sgPattern = "(.*)=\\?(.*)".r
          val sgs = 
            for (sg <- sgoals.split("\\|")) yield {
              sg match {
                case sgPattern(lhs, rhs) => (lhs.toString, rhs.toString)
              }
            }
          cons.addGoal(sgs.toList)
        }
        case "DOMAINS" => section = "domains"
        case "PROBLEM" => {
          section = "problem"
          cons.newSubproblem()
        }
      }
    }

    cons.solveLazy(timeout)
  }
}
