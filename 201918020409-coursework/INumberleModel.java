import java.util.List;

public interface INumberleModel {
    int MAX_ATTEMPTS = 6;

    void initialize();
    boolean processInput(String input);
    boolean isGameOver();
    boolean isGameWon();
    boolean isSetErrorMessage();
    String getTargetNumber();
    StringBuilder getCurrentGuess();
    int getRemainingAttempts();
    void startNewGame();
    String getCurrentFeedback();
    void setDisplayErrorMessage(boolean b);
    void setDisplayTargetEquation(boolean b);
    void setRandomEquationSelection(boolean b);
    void setRandomEquationGUI(boolean b);

}