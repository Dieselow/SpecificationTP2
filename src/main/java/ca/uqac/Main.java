package ca.uqac;

import stev.booleans.Not;
import stev.booleans.And;
import stev.booleans.Or;
import stev.booleans.Implies;
import stev.booleans.BooleanFormula;
import stev.booleans.PropositionalVariable;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;


import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

/**
 * Made By Louis Dumont and Sebastien Mireau for the class 8INF958 at UQAC
 * 
 */
public class Main {


    public static String SUDOKU = "#26###81#3##7#8##64###5###7#5#1#7#9###39#51###4#3#2#5#2###3###15##2#4##9#38###46#";

    public static void main(String[] args) {
        if(args.length != 1){
            System.out.println("Usage: ./executable StringRepresentingSudokuProblem");
            System.out.println("Example: ./executable #26###81#3##7#8##64###5###7#5#1#7#9###39#51###4#3#2#5#2###3###15##2#4##9#38###46#");
            System.exit(1);
        }

        String sudoku = args[0];
        if (sudoku.length() != 81){
            System.out.println("Length of string representing sudoku must be 81");
            System.exit(1);
        }

        SolveSudoku(sudoku);
    }

    private static PropositionalVariable[][][] createVProps(){
        PropositionalVariable[][][] variablesProposition = new PropositionalVariable[9][9][9];
            for(int row=0; row<9; row++){
                for(int col=0; col<9; col++){
                    for(int num=0; num<9; num++){
                        variablesProposition[row][col][num] = new PropositionalVariable(String.format("%d%d%d", row, col, num));
                    }
                }
            }
        return variablesProposition;
    }

    private static void printSudoku(String sudoku) {
        if(sudoku.length() != 81){
            System.out.println("Length of string representing sudoku must be 81");
            System.exit(1);
        }

        for(int i=0; i<sudoku.length(); i++){
            if(i != 0){
                if(i%9 == 0){
                    System.out.println();
                }
                // Print vertical bar every 3 cell
                else if(i%3 == 0){
                    System.out.print("|");
                }

            }
            // Print a horizontal every 3 row
            if(i/(9*3) > (i-1)/(9*3)){
                System.out.println("--- --- --- ");
            }

            char c = sudoku.charAt(i);
            if(c == '#'){
                System.out.print(" ");
            } else{
                System.out.print(c);
            }
        }
        System.out.println();
    }

    private static void SolveSudoku(String sudoku) {
        printSudoku(sudoku);
        BooleanFormula sudokuRules = createFormula();
        // System.out.println("Boolean formula in CNF format was successfully generated");
        int[][] clauses = sudokuRules.getClauses();
        Map<Integer, String> associations = getInvertedAssociations(sudokuRules);
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(9*9*9);
        solver.setExpectedNumberOfClauses(clauses.length + getNumberOfConstraintsSudoku(sudoku));

        for(int i=0; i<clauses.length; i++){
            try {
                solver.addClause(new VecInt(clauses[i]));
            } catch (ContradictionException e) {
                System.out.println(e);
                System.out.println(Arrays.toString(clauses[i]));
            }
        }

        solver = addPreFilledNumber(sudoku, solver, sudokuRules.getVariablesMap());
        IProblem problem = solver;

        try {
            if (problem.isSatisfiable()) {
                System.out.println("Problem is solvable");
                char[] sudokuResult = new char[81];
                int i = 0;
                for (int var : problem.model()) {
                    // Only get numbers in cell
                    if (var > 0) {
                        // [0] -> row, [1] -> column, [2] -> number
                        // We get each cell in order of the sudoku and only one
                        // number is set in one cell so we can safely iterate
                        // Without checking row and column of associations.get(var)
                        int numInCell = Character.getNumericValue(associations.get(var).charAt(2));
                        sudokuResult[i] =  Character.forDigit(numInCell+1, 10);
                        i++;
                    }
                }
                printSudoku(String.valueOf(sudokuResult));
            } else {
                System.out.println("Problem is not solvable");
            }
        } catch (TimeoutException e) {
            System.out.println(e);
        }
    }

    /*
     * This method calculate the number of additionals constraint to the boolean formula
     * based on the number pre-filled in the grid
     */
    private static int getNumberOfConstraintsSudoku(String sudoku){
        int counter = 0;
        for(int i=0; i<sudoku.length(); i++){
            if(sudoku.charAt(i) != '#'){
                counter++;
            }
        }
        return counter;
    }

    private static ISolver addPreFilledNumber(String sudoku, ISolver solver, Map<String, Integer> associations){
        // Iterate over the string representing the sudoku
        for(int i=0; i<sudoku.length(); i++){
            char c = sudoku.charAt(i);
            // If we get something different than a # then it's a number pre-filled
            if(c != '#'){
                // We transform its index in the string as coordinate in the grid
                int row = i/9;
                int col = i%9;
                // We get the associated integer for XXX propVar
                int varNum = associations.get(String.format("%d%d%d", row, col, Character.getNumericValue(c)-1));
                // We add a clause containing only the XXX propVar, so it must be True
                try {
                    solver.addClause(new VecInt(new int[]{varNum}));
                } catch (ContradictionException e) {
                    System.out.println(e);
                    System.out.println("Sudoku grid seems invalid");
                }
            }
        }
        return solver;
    }

    private static Map<Integer, String> getInvertedAssociations(BooleanFormula b){
        Map<String,Integer> associations = b.getVariablesMap();
        Map<Integer,String> invertedAssociations = new HashMap<Integer,String>();
        String s = null;

        for(int row=0; row<9; row++){
            for(int col=0; col<9; col++){
                for(int num=0; num<9; num++){
                    s = String.format("%d%d%d", row, col, num);
                    invertedAssociations.put(associations.get(s), s);
                }
            }
        }
        return invertedAssociations;
    }

    private static BooleanFormula createFormula(){
        PropositionalVariable[][][] vProps = createVProps();
        BooleanFormula cond1 = createConditionOneNumberByCell(vProps);
        BooleanFormula cond2 = createConditionUniqueNumberByRow(vProps);
        BooleanFormula cond3 = createConditionUniqueNumberByCol(vProps);
        BooleanFormula cond4 = createConditionUniqueNumberBySubGrid(vProps);

        And fullFormula = new And(cond1, cond2, cond3, cond4);

        return BooleanFormula.toCnf(fullFormula);
    }

    private static BooleanFormula createConditionUniqueNumberByRow(PropositionalVariable[][][] vProps){
        BooleanFormula[] andsRow = new BooleanFormula[81];
        int counter = 0;

        // Similar but adapted from createConditionOneNumberByCell
        for(int row=0; row<9; row++){
            for(int num=0; num<9; num++){
                BooleanFormula[] impliesNum = new Implies[9];

                for(int col=0; col<9; col++){
                    BooleanFormula[] andsCol = new Not[8];

                    for(int otherCol=0; otherCol<8; otherCol++){
                        andsCol[otherCol] = new Not(vProps[row][(otherCol+col+1)%9][num]);
                    }
                    impliesNum[col] = new Implies(vProps[row][col][num] , new And(andsCol));
                }
                andsRow[counter] = new And(impliesNum);
                counter++;
            }
        }
        BooleanFormula fullCondition = new And(andsRow);
        return fullCondition;
    }

    private static BooleanFormula createConditionUniqueNumberByCol(PropositionalVariable[][][] vProps){
        BooleanFormula[] andsCol = new BooleanFormula[81];
        int counter = 0;

        // Similar but adapted from createConditionOneNumberByCell
        for(int col=0; col<9; col++){
            for(int num=0; num<9; num++){
                BooleanFormula[] impliesNum = new Implies[9];

                for(int row=0; row<9; row++){
                    BooleanFormula[] andsRow = new Not[8];

                    for(int otherRow=0; otherRow<8; otherRow++){
                        andsRow[otherRow] = new Not(vProps[(otherRow+row+1)%9][col][num]);
                    }
                    impliesNum[row] = new Implies(vProps[row][col][num] , new And(andsRow));
                }
                andsCol[counter] = new And(impliesNum);
                counter++;
            }
        }
        BooleanFormula fullCondition = new And(andsCol);
        return fullCondition;
    }

    private static BooleanFormula createConditionUniqueNumberBySubGrid(PropositionalVariable[][][] vProps){
        BooleanFormula[] andsSubGrid = new BooleanFormula[81];
        int counter = 0;

        // These loops divide the sudoku grid in subgrid of 3x3
        // It iterate through each cell of the subgrid to create
        // the required constraints for the boolean formula
        for(int subGridRow=0; subGridRow<3; subGridRow++){
            for(int subGridCol=0; subGridCol<3; subGridCol++){
                // For each number we iterate all cells of the subgrid
                for(int num=0; num<9; num++){
                    BooleanFormula[] impliesNum = new Implies[9];
                    int impliesNumCounter = 0;

                    for(int row=0; row<3; row++){
                        for(int col=0; col<3; col++){
                            int realRow = subGridRow*3+row;
                            int realCol = subGridCol*3+col;
                            int numSubGriddCounter = 0;
                            BooleanFormula[] numSubGrid = new Not[8];

                            // We iterate a second time the subgrid to add that if the number is set in one cell
                            // Then it must be not set on all other cells of the subgrid
                            for(int otherRow=0; otherRow<3; otherRow++){
                                for(int otherCol=0; otherCol<3; otherCol++){
                                    int realOtherRow = (row+ otherRow + 1) %3 + subGridRow*3;
                                    int realOtherCol = (col+ otherCol + 1) %3 + subGridCol*3;
                                    if(realOtherCol == realCol && realOtherRow == realRow) continue;

                                    numSubGrid[numSubGriddCounter] = new Not(vProps[realOtherRow][realOtherCol][num]);
                                    numSubGriddCounter++;
                                }
                            }
                            impliesNum[impliesNumCounter] = new Implies(vProps[realRow][realCol][num], new And(numSubGrid));
                            impliesNumCounter++;
                        }
                    }
                    andsSubGrid[counter] = new And(impliesNum);
                    counter++;
                }
            }
        }
        BooleanFormula fullCondition = new And(andsSubGrid);
        return fullCondition;
    }

    private static BooleanFormula createConditionOneNumberByCell(PropositionalVariable[][][] vProps){
        BooleanFormula[] andsCell = new BooleanFormula[81];
        int counter = 0;

        for(int row=0; row<9; row++){
            for(int col=0; col<9; col++){
                BooleanFormula[] impliesCell = new Implies[9];
                BooleanFormula[] t = new PropositionalVariable[9];

                // Conditions -> Chaque case ne peut contenir qu’un seul chiffre
                // This loop create (1 -2 -3 -4 -5 -6 -7 -8 -9) for each number in one cell
                for(int num=0; num<9; num++){
                    BooleanFormula[] andsNum = new Not[8];
                    t[num] = vProps[row][col][num];

                    // iterate for each other numbers
                    for(int otherNumber=0; otherNumber<8; otherNumber++){
                        andsNum[otherNumber] = new Not(vProps[row][col][(otherNumber+num+1)%9]);
                    }
                    // We create the And condition (1 & !2 & !3 & !4 & !5 & !6 & !7 & !8 & !9) for one Cell of the Sudoku
                    impliesCell[num] = new Implies(vProps[row][col][num], new And(andsNum));
                }
                // We create the Or condition for all possibility of one Cell of the sudoku
                andsCell[counter] = new And(new And(impliesCell), new Or(t));
                counter++;
            }
        }
        // We create the And condition to join all boolean formula of all cells
        BooleanFormula fullCondition = new And(andsCell);
        return fullCondition;
    }
}
