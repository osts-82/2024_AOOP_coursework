import java.util.Stack;
// This class is used for validation user input, and make sure the BODMAS is meet
public class EquationValidator {
    //This method is to make sure user input 7 digit and can only be 0-9 or +-*/=.
    // Precondition: None.
    // Post-condition: Returns true if the input string satisfies the length and character constraints; otherwise, returns false
    //@ requires input != null;
    //@ ensures \result == (input.length() == 7 && (\forall int i; 0 <= i && i < input.length(); Character.isDigit(input.charAt(i)) || "+-*/=".indexOf(input.charAt(i)) != -1));
    public static boolean isValidInput(String input) {
        // Check if input length is 7 characters
        if (input.length() != 7) {
            System.out.println("Need 7 digit");
            return false;
        }
        // Check if each character is a digit or arithmetic sign
        for (char c : input.toCharArray()) {
            if (!Character.isDigit(c) && "+-*/=".indexOf(c) == -1) {
                System.out.println("You need input 0-9 or +-*/= ");
                return false;
            }
        }
        return true;
    }


    //This method is to make sure the BODMAS, and if left side equals to right side
    // Precondition: None.
    // Post-condition: Returns true if the input equation is valid and satisfies the BODMAS and equality constraints; otherwise, returns false.
    //@ requires input != null;
    //@ ensures \result == (sides.length == 2 && calculateEquation(sides[0]) == calculateEquation(sides[1]));
    public static boolean isValidEquation(String input) {
        // Check if the input is null or empty
        if (input == null || input.isEmpty()) {
            return false;
        }
        // Remove any leading or trailing whitespace (actually already be done by isValidInput() method)
        input = input.trim();
        // Split the equation into left side and right side based on the equals sign
        String[] sides = input.split("=");
        // Check if the equation has left and right sides
        if (sides.length != 2) {
            return false;
        }
        // Evaluate both sides of the equation
        int leftResult = calculateEquation(sides[0]);
        int rightResult = calculateEquation(sides[1]);
        //compare if left = right
        if(leftResult != rightResult){
            System.out.println("Left side: " + leftResult + " is Not equal to Right side: " + rightResult);
        }
        // Check if the evaluated left side matches the evaluated right side
        return leftResult == rightResult;
    }


    // Method to calculate the result of a given mathematical expression
    // Precondition: The input expression should be a valid mathematical expression.
    // Post-condition: Returns the result of the evaluation of the input expression.
    //@ requires expression != null;
    //@ ensures \result >= 0;
    private static int calculateEquation(String expression) {
        // Stack to store numbers in the expression
        Stack<Integer> numbers = new Stack<>();
        // Stack to store operators in the expression
        Stack<Character> operators = new Stack<>();

        // Loop through each character in the expression
        for (int i = 0; i < expression.length(); i++) {
            char c = expression.charAt(i);
            if (Character.isDigit(c)) {
                // Convert the character to integer value
                int num = c - '0';
                // Continue reading characters until a non-digit character is found
                while (i + 1 < expression.length() && Character.isDigit(expression.charAt(i + 1))) {
                    // Construct the complete number
                    num = num * 10 + (expression.charAt(i + 1) - '0');
                    // Move to the next character
                    i++;
                }
                // Push the number onto the stack
                numbers.push(num);
                // If the character is a multiplication or division operator
            } else if (c == '*' || c == '/') {
                // While there are operators on the stack with higher precedence
                while (!operators.isEmpty() && (operators.peek() == '*' || operators.peek() == '/')) {
                    // Process the operation
                    processOperation(numbers, operators);
                }
                // Push the current operator onto the stack
                operators.push(c);
                // If the character is an addition or subtraction operator
            } else if (c == '+' || c == '-') {
                while (!operators.isEmpty() && (operators.peek() == '*' || operators.peek() == '/' || operators.peek() == '+' || operators.peek() == '-')) {
                    processOperation(numbers, operators);
                }
                operators.push(c);
            }
        }
        // Process any remaining operations
        while (!operators.isEmpty()) {
            processOperation(numbers, operators);
        }

        return numbers.pop();
    }

    // Method to process an operation (addition, subtraction, multiplication, division)
    // Precondition: The input stacks numbers and operators should not be empty.
    // Post-condition: Performs the specified arithmetic operation on the top two elements of the numbers stack and pushes the result back onto the numbers stack.
    //@ requires !operators.isEmpty();
    //@ modifies numbers;
    //@ ensures !numbers.isEmpty();
    private static void processOperation(Stack<Integer> numbers, Stack<Character> operators) {
        char op = operators.pop();
        int num2 = numbers.pop();
        int num1 = numbers.pop();
        int result = 0;
        switch (op) {
            case '+':
                result = num1 + num2;
                break;
            case '-':
                result = num1 - num2;
                break;
            case '*':
                result = num1 * num2;
                break;
            case '/':
                if (num2 != 0) {
                    result = num1 / num2;
                } else {
                    // Throw an exception for division by zero
                    throw new ArithmeticException("Division by zero");
                }
                break;
        }
        // Push the result of the operation onto the numbers stack
        numbers.push(result);
    }
}
