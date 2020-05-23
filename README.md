# Lprog-Projeto


We'll be using bytes. Instructions are 2 bytes long and memory/instructions are stored in big-endian format.
 
 Caution: coq bytes are stored in little endian format
 
 - Modelling this machine requires several components:
    - Modelling main memory (Sounds easy, list of bytes?).
    - Modelling the stack (We've also done this before).
    - Modelling "GPU" memory (Even if I don't think there's a way to display it on Coq, we still need it for some instructions.
    - Modelling the instruction set (We can write the equivalent of exec that we've been using in class.
    - Modelling the "CPU" (Hardest part for sure):
        - Modelling the 16 registers (V0-VF) and the I register.
        - Modellling the Program Counter.
        - Modelling the timer registers (Don't see how it's possible).
        - Modelling input (Also not sure).

 For more info see https://en.wikipedia.org/wiki/CHIP-8.