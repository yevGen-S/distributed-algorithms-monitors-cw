#define emptyC(C) (C.waiting == 0)

typedef Condition {
    bool gate; /* Для блокирования процесса */
    byte waiting; /* Кол-во ожидающих условия процессов */
}

bool lock = false;

inline enterMonitor() {
    atomic {
        !lock;
        lock = true;
    }
}

inline leaveMonitor() {
    lock = false;
}

/* Открывает замок монитора и ждет true для C переменной */
inline waitC(C) { 
    atomic {
        C.waiting++;
        lock = false;
        C.gate;      
        C.gate = false;
        C.waiting--;
    }
}

/* Ставит gate = true; заблокированный процесс может продолжить */
inline signalC(C) { /
    atomic {
        if
        :: (C.waiting > 0) -> {
            C.gate = true;
            !lock;
            lock = true;
        }
        :: else -> break;
        fi;
    }
}