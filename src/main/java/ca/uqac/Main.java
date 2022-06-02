package ca.uqac;

import stev.booleans.Implies;
import stev.booleans.Not;
import stev.booleans.And;
import stev.booleans.Or;
import stev.booleans.BooleanFormula;
import stev.booleans.PropositionalVariable;

import java.util.HashMap;

import java.util.Map;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;


public class Main {

    public static String SUDOKU = "#26###81#3##7#8##64###5###7#5#1#7#9###39#51###4#3#2#5#1###3###15##2#4##9#38###46#";

    public static void main(String[] args){
        //SolveSudoku(SUDOKU);

     

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
        And fullCondition = new And();

        // Similar but adapted from createConditionOneNumberByCell
        for(int row=0; row<9; row++){
            for(int num=0; num<9; num++){
                Or or_row = new Or();
                for(int col=0; col<9; col++){
                    And and_row = new And(vProps[row][col][num]);
                    for(int other_col=0; other_col<8; other_col++){
                        Not n = new Not(vProps[row][(other_col+col+1)%9][num]);
                        and_row = new And(and_row, n);
                    }
                    or_row = new Or(or_row, BooleanFormula.toCnf(and_row));
                }
                fullCondition = new And(fullCondition, or_row);
            }
        }
        return BooleanFormula.toCnf(fullCondition);
    }

    private static BooleanFormula createConditionUniqueNumberByCol(PropositionalVariable[][][] vProps){
        And fullCondition = new And();

        //HAVE ->  (000 & !100 & !200 & !300 & !400 & !500 & !600 & !700 & !800)) | (010
        // WANT -> (000 & !100 & !200 & !300 & !400 & !500 & !600 & !700 & !800)) | (100 
        for(int num=0; num<9; num++){
            for(int row=0; row<9; row++){
                Or or_col = new Or();
                for(int col=0; col<9; col++){
                    And and_col = new And(vProps[row][col][num]);
                    for(int other_row=0; other_row<8; other_row++){
                        Not n = new Not(vProps[(other_row+row+1)%9][col][num]);
                        and_col = new And(and_col, n);
                    }
                    or_col = new Or(or_col, BooleanFormula.toCnf(and_col));
                }
                fullCondition = new And(fullCondition, or_col);
            }
        }
        return BooleanFormula.toCnf(fullCondition);
    }

    private static BooleanFormula createConditionUniqueNumberBySubGrid(PropositionalVariable[][][] vProps){
        And fullCondition = new And();

        // These loops divide the sudoku grid in subgrid of 3x3
        // It iterate through each cell of the subgrid to create
        // the required constraints for the boolean formula
        for(int subGridRow=0; subGridRow<3; subGridRow++){
            for(int subGridCol=0; subGridCol<3; subGridCol++){
                // For each number we iterate all cells of the subgrid
                for(int num=0; num<9; num++){
                    Or or_grid = new Or();
                    for(int row=0; row<3; row++){
                        for(int col=0; col<3; col++){
                            int real_row = subGridRow*3+row;
                            int real_col = subGridCol*3+col;
                            And and_grid = new And(vProps[real_row][real_col][num]);

                            // We iterate a second time the subgrid to add that if the number is set in one cell
                            // Then it must be not set on all other cells of the subgrid
                            for(int other_row=0; other_row<3; other_row++){
                                for(int other_col=0; other_col<3; other_col++){
                                    int real_other_row = (row+ other_row + 1) %3 + subGridRow*3;
                                    int real_other_col = (col+ other_col + 1) %3 + subGridCol*3;
                                    if(real_other_col == real_col && real_other_row == real_row) continue;

                                    Not n = new Not(vProps[real_other_row][real_other_col][num]);
                                    and_grid = new And(and_grid, n);
                                }
                            }
                            or_grid = new Or(or_grid, BooleanFormula.toCnf(and_grid));
                        }
                    }
                    fullCondition = new And(fullCondition, or_grid);
                }
            }
        }
        return BooleanFormula.toCnf(fullCondition);
    }

    private static BooleanFormula createConditionOneNumberByCell(PropositionalVariable[][][] vProps){
        BooleanFormula[] ors_cell_cnf = new BooleanFormula[81];
        int counter = 0;

        for(int row=0; row<9; row++){
            for(int col=0; col<9; col++){
                BooleanFormula[] ands_cell_cnf = new And[9];

                // Conditions -> Chaque case ne peut contenir qu’un seul chiffre
                // This loop create (1 -2 -3 -4 -5 -6 -7 -8 -9) for each number in one cell
                for(int num=0; num<9; num++){
                    And and_cell = new And(vProps[row][col][num]);
                    // iterate for each other numbers

                    for(int otherNumber=0; otherNumber<8; otherNumber++){
                        Not n = new Not(vProps[row][col][(otherNumber+num+1)%9]);
                        and_cell = new And(and_cell, n);
                    }
                    // We add the new boolean formula to the others with xor
                    ands_cell_cnf[num] = BooleanFormula.toCnf(and_cell);
                }
                System.out.println(BooleanFormula.toCnf(new Or(ands_cell_cnf[0], ands_cell_cnf[1], ands_cell_cnf[2], ands_cell_cnf[3], ands_cell_cnf[4], ands_cell_cnf[5])));
                System.exit(0);
                ors_cell_cnf[counter] = new Or(ands_cell_cnf);
                counter++;
            }
        }
        BooleanFormula fullCondition = new And(ors_cell_cnf);
        return fullCondition;
    }
}
