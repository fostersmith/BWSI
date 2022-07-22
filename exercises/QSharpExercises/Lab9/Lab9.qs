// Lab 9: Shor's Algorithm
// Copyright 2021 The MITRE Corporation. All Rights Reserved.

namespace Lab9 {

    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Measurement;


    /// # Summary
    /// In this exercise, you must implement the quantum modular
    /// exponentiation function: |o> = a^|x> mod b.
    /// |x> and |o> are input and output registers respectively, and a and b
    /// are classical integers.
    /// 
    /// # Input
    /// ## a
    /// The base power of the term being exponentiated.
    /// 
    /// ## b
    /// The modulus for the function.
    /// 
    /// ## input
    /// The register containing a superposition of all of the exponent values
    /// that the user wants to calculate; this superposition is arbitrary.
    /// 
    /// ## output
    /// This register must contain the output |o> of the modular
    /// exponentiation function. It will start in the |0...0> state.
    operation Exercise1 (
        a : Int,
        b : Int,
        input : Qubit[],
        output : Qubit[]
    ) : Unit {
        // Note: For convenience, you can use the
        // Microsoft.Quantum.Math.ExpModI() function to calculate a modular
        // exponent classically. You can use the
        // Microsoft.Quantum.Arithmetic.MultiplyByModularInteger() function to
        // do an in-place quantum modular multiplication.

        let leo = LittleEndian(output);
        let N = Length(input);
        X(output[Length(output)-1]);

        // TODO
        for i in 0..N-1 {
            let qubit = input[i];
            Controlled MultiplyByModularInteger([qubit], (ExpModI(a, 2^(N-i-1), b), b, leo));
        }

    }


    /// # Summary
    /// In this exercise, you must implement the quantum subroutine of Shor's
    /// algorithm. You will be given a number to factor and some guess to a
    /// possible factor - both of which are integers.
    /// You must set up, execute, and measure the quantum circuit.
    /// You should return the fraction that was produced by measuring the
    /// result at the end of the subroutine, in the form of a tuple:
    /// the first value should be the number you measured, and the second
    /// value should be 2^n, where n is the number of qubits you use in your
    /// input register.
    /// 
    /// # Input
    /// ## numberToFactor
    /// The number that the user wants to factor. This will become the modulus
    /// for the modular arithmetic used in the subroutine.
    /// 
    /// ## guess
    /// The number that's being guessed as a possible factor. This will become
    /// the base of exponentiation for the modular arithmetic used in the 
    /// subroutine.
    /// 
    /// # Output
    /// A tuple representing the continued fraction approximation that the
    /// subroutine measured. The first value should be the numerator (the
    /// value that was measured from the qubits), and the second value should
    /// be the denominator (the total size of the input space, which is 2^n
    /// where n is the size of your input register).
    operation Exercise2 (
        numberToFactor : Int,
        guess : Int
    ) : (Int, Int) {
        // Hint: you can use the Microsoft.Quantum.Arithmetic.MeasureInteger()
        // function to measure a whole set of qubits and transform them into
        // their integer representation.

        // NOTE: This is a *probablistic* test. There is a chance that the
        // unit test fails, even if you have the correct answer. If you think
        // you do, run the test again. Also, look at the output of the test to
        // see what values you came up with versus what the system expects.

        let outputSize = Ceiling(Lg(IntAsDouble(numberToFactor + 1)));
        use (input, output) = (Qubit[outputSize * 2], Qubit[outputSize]);

        ApplyToEach(H, input);

        let bei = BigEndian(input);

        Exercise1(guess, numberToFactor, input, output);

        Adjoint QFT(bei);

        let numerator = MeasureInteger(BigEndianAsLittleEndian(bei));
        let demoninator = 2^Length(input);

        ResetAll(output);

        return (numerator, demoninator);
    }


    /// # Summary
    /// In this exercise, you will be given an arbitrary numerator and
    /// denominator for a fraction, along with some threshold value for the
    /// denominator.
    /// Your goal is to return the largest convergent of the continued
    /// fraction that matches the provided number, with the condition that the
    /// denominator of your convergent must be less than the threshold value.
    /// 
    /// Using the example from the lecture section, if you are given the
    /// number 341 / 512 with a threshold of 21, the most accurate convergent
    /// that respects this threshold is 2 / 3, so that's what you would return.
    /// 
    /// # Input
    /// ## numerator
    /// The numerator of the original fraction
    /// 
    /// ## denominator
    /// The denominator of the original fraction
    /// 
    /// ## denominatorThreshold
    /// A threshold value for the denominator. The continued fraction
    /// convergent that you find must be less than this value. If it's higher,
    /// you must return the previous convergent.
    /// 
    /// # Output
    /// A tuple representing the convergent that you found. The first element
    /// should be the numerator, and the second should be the denominator.
    function Exercise3 (
        numerator : Int,
        denominator : Int,
        denominatorThreshold : Int
    ) : (Int, Int) {
        Message($"Numerator: {numerator} Denominator: {denominator} Threshold: {denominatorThreshold}");
        if(numerator == 0){
            return (0, 1);
        }

        mutable Pi = numerator;
        mutable Qi = denominator;
        mutable nvals = [1, 0]; //(n_i, n_i-1)
        mutable dvals = [0, 1];
        mutable i = 0;
        mutable ri = 100;
        while(dvals[0] < denominatorThreshold and ri != 0){
            let ai = Pi/Qi;
            set ri = Pi%Qi;
            let tempn = nvals[0];
            let tempd = dvals[0];
            set nvals w/= 0 <- ai*nvals[0] + nvals[1];
            set dvals w/= 0 <- ai*dvals[0] + dvals[1];
            set nvals w/= 1 <- tempn;
            set dvals w/= 1 <- tempd;
            set Pi = Qi;
            set Qi = ri;
            set i += 1;
        }

        mutable ind = 0;
        if(dvals[0] >= denominatorThreshold){
            set ind = 1;
        }
        return (nvals[ind], dvals[ind]);
    }


    /// # Summary
    /// In this exercise, you are given two integers - a number that you want
    /// to find the factors of, and an arbitrary guess as to one of the
    /// factors of the number. This guess was already checked to see if it was
    /// a factor of the number, so you know that it *isn't* a factor. It is
    /// guaranteed to be co-prime with numberToFactor.
    /// 
    /// Your job is to find the period of the modular exponentation function
    /// using these two values as the arguments. That is, you must find the
    /// period of the equation y = guess^x mod numberToFactor.
    /// 
    /// # Input
    /// ## numberToFactor
    /// The number that the user wants to find the factors for
    /// 
    /// ## guess
    /// Some co-prime integer that is smaller than numberToFactor
    /// 
    /// # Output
    /// The period of y = guess^x mod numberToFactor.
    operation Exercise4 (numberToFactor : Int, guess : Int) : Int
    {
        // Note: you can't use while loops in operations in Q#.
        // You'll have to use a repeat loop if you want to run
        // something several times.

        // Hint: you can use the
        // Microsoft.Quantum.Math.GreatestCommonDivisorI()
        // function to calculate the GCD of two numbers.

        mutable (_, dOld) = newIOverP(numberToFactor, guess);
        if(isPeriod(guess, numberToFactor, dOld)){
            return dOld;
        }
        mutable dNew = 0;
        repeat{
            let (_, newD) = newIOverP(numberToFactor, guess);
            set dNew = newD;
        } until (dOld != dNew);
        if(isPeriod(guess, numberToFactor, dNew)){
            return dNew;
        }
        repeat{
            let temp = dNew;
            set dNew = (dOld*dNew)/GreatestCommonDivisorI(dOld, dNew);
            set dOld = temp;
        } until (isPeriod(guess, numberToFactor, dNew));
        return dNew;
    }

    operation newIOverP(b: Int, a: Int) : (Int, Int) {
        repeat{
            let (xi, twoToTheN) = Exercise2(b, a);
            if(xi>0){
                return Exercise3(xi,twoToTheN,b);
            }
        } until (false);
        return (0,0);
    }

    operation isPeriod(a:Int, b: Int, p: Int) : Bool {
        return (a^p)%b == 1;
    }


    /// # Summary
    /// In this exercise, you are given a number to find the factors of,
    /// a guess of a factor (which is guaranteed to be co-prime), and the
    /// period of the modular exponentiation function that you found in
    /// Exercise 4.
    /// 
    /// Your goal is to use the period to find a factor of the number if
    /// possible.
    /// 
    /// # Input
    /// ## numberToFactor
    /// The number to find a factor of
    /// 
    /// ## guess
    /// A co-prime number that is *not* a factor
    /// 
    /// ## period
    /// The period of the function y = guess^x mod numberToFactor.
    /// 
    /// # Output
    /// - If you can find a factor, return that factor.
    /// - If the period is odd, return -1.
    /// - If the period doesn't work for factoring, return -2.
    function Exercise5 (
        numberToFactor : Int,
        guess : Int, period : Int
    ) : Int {

        if(period%2 !=0){
            return -1;
        }

        let (aRaisedToThePOverTwoMinusOne, aRaisedToThePOverTwoPlusOne) = (guess^(period/2)-1, guess^(period/2)+1);

        if(aRaisedToThePOverTwoPlusOne % numberToFactor == 0){
            return -2;
        }

        let b0 = GreatestCommonDivisorI(numberToFactor, aRaisedToThePOverTwoPlusOne);
        //let b1 = GreatestCommonDivisorI(numberToFactor, aRaisedToThePOverTwoMinusOne);

        return b0;
    }
}
