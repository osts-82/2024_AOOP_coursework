import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

public class NumberleModelTest {
    private NumberleModel model;
    @Before
    public void setUp() throws Exception {
        model = new NumberleModel();
        model.initialize();
    }

    @After
    public void tearDown() throws Exception {
        model = null;
    }


    /** Scenario: Test playing the game with error message display,
     *             all 6 guesses are invalid inputs
     *  Pre-condition: The game is initialized and the target number is set (2+3*2=8),
     *                  the error message flag is set to true.
     *  Input: First guess: "+++++++"; Second guess: "1234567"; Third Guess: "1+2*3=0"
     *  Fourth guess: "2+4-5+8"; fifth guess: "@#$%^&)"; Sixth guess: "1~lsetj"
     *  Post-condition: The game is not over, still have attempts = 6.
     */
    @Test
    public void scenarios1() {
        //pre condition:
        model.setDisplayErrorMessage(true);
        assertEquals(model.isSetErrorMessage(), true);
        assertEquals(model.getTargetNumber(), "2+3*2=8");

        //first guess, invalid input do not count one attempt
        assertFalse(model.processInput("+++++++"));
        assertEquals(model.getRemainingAttempts(), 6);
        assertFalse(model.isGameWon());

        //second guess, invalid equation do not count one attempt
        assertFalse(model.processInput("1234567"));
        assertEquals(model.getRemainingAttempts(), 6);
        assertFalse(model.isGameWon());

        //Third guess, valid input, but not equals to target equation
        assertFalse(model.processInput("1+2*3=0"));
        assertEquals(model.getRemainingAttempts(), 6);
        assertFalse(model.isGameWon());

        //4th guess, valid input,  equals to target equation game won
        assertFalse(model.processInput("2+4-5+8"));
        assertEquals(model.getRemainingAttempts(), 6);
        assertFalse(model.isGameWon());

        //5th guess, valid input,  equals to target equation game won
        assertFalse(model.processInput("@#$%^&)"));
        assertEquals(model.getRemainingAttempts(), 6);
        assertFalse(model.isGameWon());

        //6th guess, valid input,  equals to target equation game won
        assertFalse(model.processInput("1~lsetj"));
        assertEquals(model.getRemainingAttempts(), 6);
        assertFalse(model.isGameWon());

        //post-condition
        assertFalse(model.isGameOver());

    }

    /** Scenario: Test playing the game with error message display,
     *             first 5 guesses are wrong and the 6th guess is right.
     *  Pre-condition: The game is initialized and the target number is set (2+3*2=8),
     *                  the error message flag is set to true.
     *  Input: First guess: "1+2+3=6"; Second guess: "2+3+4=9"; Third Guess: "3+2*2=7"
     *  Fourth guess: "2+3-0=5"; fifth guess: "4+2-3=3"; Sixth guess: "2+3*2=8"
     *
     *  Post-condition: The game is won game is over, attempts = 0.
     */
    @Test
    public void scenarios2() {
        //precondition:
        model.setDisplayErrorMessage(true);
        assertEquals(model.isSetErrorMessage(), true);
        assertEquals(model.getTargetNumber(), "2+3*2=8");

        //first guess, 1+2+3=6
        assertTrue(model.processInput("1+2+3=6"));
        assertEquals(model.getRemainingAttempts(), 5);
        assertFalse(model.isGameWon());

        //second guess, 2+3+4=9
        assertTrue(model.processInput("2+3+4=9"));
        assertEquals(model.getRemainingAttempts(), 4);
        assertFalse(model.isGameWon());

        //Third guess, 3+2*2=7
        assertTrue(model.processInput("3+2*2=7"));
        assertEquals(model.getRemainingAttempts(), 3);
        assertFalse(model.isGameWon());

        //4th guess, 2+3-0=5
        assertTrue(model.processInput("2+3-0=5"));
        assertEquals(model.getRemainingAttempts(), 2);
        assertFalse(model.isGameWon());

        //5th guess, 4+2-3=3
        assertTrue(model.processInput("4+2-3=3"));
        assertEquals(model.getRemainingAttempts(), 1);
        assertFalse(model.isGameWon());

        //6th guess, 2+3*2=8
        assertTrue(model.processInput("2+3*2=8"));
        assertEquals(model.getRemainingAttempts(), 0);

        //post-condition
        assertTrue(model.isGameWon());
        assertTrue(model.isGameOver());
        assertEquals(model.getRemainingAttempts(), 0);
    }

    /** Scenario: Test playing the game with error message display,
     *             and test the feedbacks for 3 false guesses and 1 correct guess
     *  Pre-condition: The game is initialized and the target number is set (2+3*2=8),
     *                  the error message flag is set to true.
     *  Input: First guess: "1+2+3=6"; Second guess: "3+2+0=5"; Third Guess: "2+3/3=3"
     *         Fourth guess: "2+3*2=8"
     *  Expected output: (1-green,2-orange,3-gray) g1:3123213; g2:2123313; g3:1113313; g4:1111111
     *                  the detail see String variable expectedFeedbackGuess1-4
     *  Post-condition: The game is won game is over, attempts = 2.
     */
    @Test
    public void scenarios3() {
        //This is the expected output of each guess:
        String expectedFeedbackGuess1 = "Green: " + "+=" + "\n" + "Orange: " + "23" + "\n" + "Gray: " + "1+6" + "\n" + "Not using: " + "045789-/*" + "\n" + "3123213";
        String expectedFeedbackGuess2 = "Green: " + "+=" + "\n" + "Orange: " + "23" + "\n" + "Gray: " + "1+605" + "\n" + "Not using: " + "4789-/*" + "\n" + "2123313";
        String expectedFeedbackGuess3 = "Green: " + "+=23" + "\n" + "Orange: " + "" + "\n" + "Gray: " + "1+605/3" + "\n" + "Not using: " + "4789-*" + "\n" + "1113313";
        String expectedFeedbackGuess4 = "Green: " + "+=23*8" + "\n" + "Orange: " + "" + "\n" + "Gray: " + "1+605/3" + "\n" + "Not using: " + "479-" + "\n" + "1111111";

        //precondition:
        model.setDisplayErrorMessage(true);
        assertEquals(model.isSetErrorMessage(), true);
        assertEquals(model.getTargetNumber(), "2+3*2=8");

        //first guess, 1+2+3=6
        assertTrue(model.processInput("1+2+3=6"));
        assertEquals(model.getRemainingAttempts(), 5);
        assertFalse(model.isGameWon());
        assertEquals(model.getCurrentFeedback(), expectedFeedbackGuess1);

        //second guess, 3+2+0=5
        assertTrue(model.processInput("3+2+0=5"));
        assertEquals(model.getRemainingAttempts(), 4);
        assertFalse(model.isGameWon());
        assertEquals(model.getCurrentFeedback(), expectedFeedbackGuess2);

        //Third guess, 2+3/3=3
        assertTrue(model.processInput("2+3/3=3"));
        assertEquals(model.getRemainingAttempts(), 3);
        assertFalse(model.isGameWon());
        assertEquals(model.getCurrentFeedback(), expectedFeedbackGuess3);

        //4th guess, 2+3*2=8
        assertTrue(model.processInput("2+3*2=8"));
        assertEquals(model.getRemainingAttempts(), 2);
        assertTrue(model.isGameWon());
        assertEquals(model.getCurrentFeedback(), expectedFeedbackGuess4);

        //post-condition
        assertTrue(model.isGameWon());
        assertTrue(model.isGameOver());
        assertEquals(model.getRemainingAttempts(), 2);
    }
}