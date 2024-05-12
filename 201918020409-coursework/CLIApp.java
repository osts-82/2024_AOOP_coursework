import java.util.Scanner;

public class CLIApp {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        INumberleModel model = new NumberleModel();

        // Ask player to set flags
        System.out.println("Do you want to set flags? (Y to set) Any other key to start right away");
        String flagChoice = scanner.nextLine().trim().toUpperCase();

        if (flagChoice.equals("Y")) {
            setFlags(scanner, model);
        }

        // Initialize the game
        model.initialize();
        System.out.println("Welcome to Numberle!");
        System.out.println("Pleas enter 0-9 and +,-,*,/ to Guess the Equation!");

        // Game loop
        while (!model.isGameOver()) {
            // Get player input
            String input = getPlayerInput();
            // Process input to get each digit color
            model.processInput(input);
            // Display feedback
            System.out.println("Number in the Last: 1-Green; 2-Orange; 3-Gary");
            System.out.println(model.getCurrentFeedback());
            if (model.isGameWon()){
                System.out.println("You have won the game! Congratulations!!!");
            }else {
                System.out.println("Now you have " + model.getRemainingAttempts() + " chances");
            }
        }
        // Display win/loss message at the end of the game
        if (!model.isGameWon()) {
            System.out.println("Sorry! You have lost the game.");
        }
    }

    // Method to get player input
    private static String getPlayerInput() {
        Scanner scanner = new Scanner(System.in);
        System.out.print("Enter your guess: ");
        String input = scanner.nextLine().trim();
        return input;
    }

    // Method to set flags
    private static void setFlags(Scanner scanner, INumberleModel model) {
        System.out.println("Set flags:");
        System.out.println("1. Display Error Message");
        System.out.println("2. Display Target Equation");
        System.out.println("3. Random Equation Selection");

        int choice;
        do {
            System.out.print("Enter flag number to set (1/2/3), or 0 to finish: ");
            while (!scanner.hasNextInt()) {
                System.out.println("Invalid input. Please enter a number.");
                scanner.next();
            }
            choice = scanner.nextInt();
            if (choice < 0 || choice > 3) {
                System.out.println("Invalid choice. Please enter a number between 0 and 3.");
            }
        } while (choice < 0 || choice > 3);  // do while loop to make sure only receive 1/2/3 or o.

        scanner.nextLine(); // Consume newline

        switch (choice) {
            case 1:
                model.setDisplayErrorMessage(true);
                System.out.println("Error Message flag set.");
                break;
            case 2:
                model.setDisplayTargetEquation(true);
                System.out.println("Target Equation flag set.");
                break;
            case 3:
                model.setRandomEquationSelection(true);
                System.out.println("Random Equation Selection flag set.");
                break;
            case 0:
                //End recursive
                return;
        }
        setFlags(scanner, model); // Recursively set flags until finished
    }


}
