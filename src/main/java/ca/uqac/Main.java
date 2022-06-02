package ca.uqac;

import stev.booleans.Implies;
import stev.booleans.Not;
import stev.booleans.And;
import stev.booleans.Or;
import stev.booleans.BooleanFormula;
import stev.booleans.PropositionalVariable;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.InstanceReader;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;


public class Main {

    public static String SUDOKU = "#26###81#3##7#8##64###5###7#5#1#7#9###39#51###4#3#2#5#1###3###15##2#4##9#38###46#";

    public static void main(String[] args){
        // testSeb();
        SolveSudoku(SUDOKU);
        //   rowConstraints();


        System.out.println("Hello world");

    }

    public static void rowConstraints(){
        BooleanFormula formula = null;
        PropositionalVariable[] prop = createPropsLouis();
        //displayArray(prop);
        BooleanFormula fullFormula = null;

        for(int j=0;j<9;j++){
            formula = null;
            Not startNot = null;
            for (int i=0;i<8;i++){
                if (startNot == null){
                    startNot = new Not(prop[(i+1)*9+j]);
                    continue;
                }
                else if(formula == null && startNot !=null){
                    formula = new And(startNot,new Not(prop[(i+1)*9+j]));
                }
                else {
                    formula = new And(formula,new Not(prop[(i+1)*9+j]));
                }

            }
            //System.out.println(BooleanFormula.toCnf(formula).toString());
            if(fullFormula == null){
                fullFormula = new Implies(prop[j],formula);
                System.out.println(fullFormula);
            }
            else {
                fullFormula = new And(fullFormula,new Implies(prop[j],formula));
            }
        }

       // System.out.println(BooleanFormula.toCnf(fullFormula).toString());

    }

    private static PropositionalVariable[] createPropsLouis(){
        PropositionalVariable[] variablesProposition = new PropositionalVariable[9*9*9];
        int row = 1;
        int col = 1;
        int num = 1;
        for(int i=0;i<9*9*9;i++){
            variablesProposition[i] = new PropositionalVariable(String.format("%d%d%d", row, col, num));
            if(num == 9){
                num=1;
                col++;
                if(col > 9){
                    col = 1;
                    row++;
                }
                continue;
            }

            num++;
        }


        return variablesProposition;
    }

    public static void displayArray(PropositionalVariable[] array){
        for (int i = 0; i < array.length; i++) {
            System.out.println(array[i]);
        }
    }
    //Utils
    public static Implies impliesNot(PropositionalVariable i, PropositionalVariable j){
        return new Implies(i, new Not(j));
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

    private static void SolveSudoku(String sudoku){
        BooleanFormula booleanFormula = createFormula();
        System.out.println("Boolean formula in CNF format was successfully generated");
        int[][] clauses = booleanFormula.getClauses();
        ISolver solver = SolverFactory.newDefault();
        solver.newVar(9*9*9);
        solver.setExpectedNumberOfClauses(clauses.length);

        for(int i=0; i<clauses.length; i++){
            try {
                solver.addClause(new VecInt(clauses[i]));
            } catch (ContradictionException e) {
                System.out.println(e);
            }
        }

        IProblem problem = solver;
        Map<Integer, String> associations = getInvertedAssociations(booleanFormula);

        try {
            if (problem.isSatisfiable()) {
                System.out.println("Problem is solvable");
                for (int var : problem.model()) {
                    // Only get var that are true
                    if (var > 0) {
                        System.out.println(associations.get(var));
                    }
                  }
            } else {
                System.out.println("Problem is not solvable");
            }
        } catch (TimeoutException e) {
            System.out.println(e);
        }
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
        System.out.println("Boolean formula is fully created, casting it to CNF...");

        return BooleanFormula.toCnf(fullFormula);
    }

    private static BooleanFormula createConditionUniqueNumberByRow(PropositionalVariable[][][] vProps){
        BooleanFormula[] orsCell = new BooleanFormula[81];
        int counter = 0;

        // Similar but adapted from createConditionOneNumberByCell
        for(int row=0; row<9; row++){
            for(int num=0; num<9; num++){
                BooleanFormula[] andsNum = new And[9];

                for(int col=0; col<9; col++){
                    BooleanFormula[] andsCol = new BooleanFormula[9];
                    andsCol[0] = vProps[row][col][num];

                    for(int otherCol=0; otherCol<8; otherCol++){
                        andsCol[otherCol+1] = new Not(vProps[(otherCol+row+1)%9][col][num]);
                    }
                    andsNum[row] = new And(andsCol);
                }
                orsCell[counter] = new Or(andsNum);
                counter++;
            }
        }
        BooleanFormula fullCondition = new And(orsCell);
        return fullCondition;
    }

    private static BooleanFormula createConditionUniqueNumberByCol(PropositionalVariable[][][] vProps){
        BooleanFormula[] orsCell = new BooleanFormula[81];
        int counter = 0;

        // Similar but adapted from createConditionOneNumberByCell
        for(int col=0; col<9; col++){
            for(int num=0; num<9; num++){
                BooleanFormula[] andsNum = new And[9];

                for(int row=0; row<9; row++){
                    BooleanFormula[] andsRow = new BooleanFormula[9];
                    andsRow[0] = vProps[row][col][num];

                    for(int otherRow=0; otherRow<8; otherRow++){
                        andsRow[otherRow+1] = new Not(vProps[(otherRow+row+1)%9][col][num]);
                    }
                    andsNum[row] = new And(andsRow);
                }
                orsCell[counter] = new Or(andsNum);
                counter++;
            }
        }
        BooleanFormula fullCondition = new And(orsCell);
        return fullCondition;
    }

    private static BooleanFormula createConditionUniqueNumberBySubGrid(PropositionalVariable[][][] vProps){
        BooleanFormula[] orsCell = new BooleanFormula[81];
        int counter = 0;

        // These loops divide the sudoku grid in subgrid of 3x3
        // It iterate through each cell of the subgrid to create
        // the required constraints for the boolean formula
        for(int subGridRow=0; subGridRow<3; subGridRow++){
            for(int subGridCol=0; subGridCol<3; subGridCol++){
                // For each number we iterate all cells of the subgrid
                for(int num=0; num<9; num++){
                    BooleanFormula[] andsNum = new And[9];
                    int andsNumCounter = 0;

                    for(int row=0; row<3; row++){
                        for(int col=0; col<3; col++){
                            int realRow = subGridRow*3+row;
                            int realCol = subGridCol*3+col;
                            int andsSubGridCounter = 0;
                            BooleanFormula[] andsSubGrid = new BooleanFormula[9];
                            andsSubGrid[andsSubGridCounter] = vProps[realRow][realCol][num];
                            andsSubGridCounter++;

                            // We iterate a second time the subgrid to add that if the number is set in one cell
                            // Then it must be not set on all other cells of the subgrid
                            for(int otherRow=0; otherRow<3; otherRow++){
                                for(int otherCol=0; otherCol<3; otherCol++){
                                    int realOtherRow = (row+ otherRow + 1) %3 + subGridRow*3;
                                    int realOtherCol = (col+ otherCol + 1) %3 + subGridCol*3;
                                    if(realOtherCol == realCol && realOtherRow == realRow) continue;

                                    andsSubGrid[andsSubGridCounter] = new Not(vProps[realOtherRow][realOtherCol][num]);
                                    andsSubGridCounter++;
                                }
                            }
                            andsNum[andsNumCounter] = new And(andsSubGrid);
                            andsNumCounter++;
                        }
                    }
                    orsCell[counter] = new Or(andsNum);
                    counter++;
                }
            }
        }
        BooleanFormula fullCondition = new And(orsCell);
        return fullCondition;
    }

    private static BooleanFormula createConditionOneNumberByCell(PropositionalVariable[][][] vProps){
        BooleanFormula[] orsCell = new BooleanFormula[81];
        int counter = 0;

        for(int row=0; row<9; row++){
            for(int col=0; col<9; col++){
                BooleanFormula[] andsCell = new And[9];

                // Conditions -> Chaque case ne peut contenir qu’un seul chiffre
                // This loop create (1 -2 -3 -4 -5 -6 -7 -8 -9) for each number in one cell
                for(int num=0; num<9; num++){
                    BooleanFormula[] andsNum = new BooleanFormula[9];
                    andsNum[0] = vProps[row][col][num];

                    // iterate for each other numbers
                    for(int otherNumber=0; otherNumber<8; otherNumber++){
                        andsNum[otherNumber+1] = new Not(vProps[row][col][(otherNumber+num+1)%9]);
                    }
                    // We create the And condition (1 & !2 & !3 & !4 & !5 & !6 & !7 & !8 & !9) for one Cell of the Sudoku
                    andsCell[num] = new And(andsNum);
                }
                // We create the Or condition for all possibility of one Cell of the sudoku
                orsCell[counter] = new Or(andsCell);
                // System.out.println(orsCell[counter]);
                // System.out.println(BooleanFormula.toCnf(orsCell[counter]));
                // System.exit(0);
                counter++;
            }
        }
        // We create the And condition to join all boolean formula of all cells
        BooleanFormula fullCondition = new And(orsCell);
        return fullCondition;
    }
}
