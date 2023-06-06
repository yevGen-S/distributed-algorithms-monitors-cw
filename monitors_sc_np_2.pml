#define READERS 3
#define WRITERS 2
#define procId (_pid - 1)
#define NO_READ_NOTIFICATION -1
#define ALL 5
#define REAL_TRUE (1 == 1)

bool emptyArr[READERS];

typedef batchT {
    byte array[READERS];
    byte pos = 0;
}

typedef monitor {
    int readers = 0;
    int writers = 0;
    int blockedReaders = 0;
    int procStartedReadNotification = NO_READ_NOTIFICATION;
    /* По умолчанию нули */
    bool blocked[ALL];

    bool lock = false;
    bool curBatch[READERS];
    bool nextBatch[READERS];
    bool isBatchWorking = false;

}

inline copyArr(fromArr, toArr){
    i = 0;
    do
    :: i < READERS -> {
        toArr[i] = fromArr[i];
        i++;
     }
    :: else -> break;
    od;
    i = 0;
}

inline enterMon() {
    atomic {
        !RW.lock;
        RW.lock = true;
    }
}

inline leaveMon() {
    atomic {
        RW.lock = false;
    }
}

inline wait() {
    printf("MSC: now wait\n");
    RW.blocked[procId] = true;
    
    leaveMon();

    !RW.blocked[procId];

    enterMon();
}

inline notifyAll() {
    printf("MSC: notifyAll\n");
    k = 0;
    do
    :: k < ALL -> {
        atomic {
            RW.blocked[k] = false;
            k++;
        }
    }
    :: else -> break;
    od;
    k = 0;
}

inline startRead() {
    enterMon();

    printf("MSC: try read\n");

    if
    :: RW.writers > 0 || !RW.isBatchWorking -> RW.curBatch[procId] = true;
    :: else -> RW.nextBatch[procId] = true;
    fi;

    do
    :: (RW.writers != 0 || RW.isBatchWorking) -> {
        RW.blockedReaders++;
        printf("MSC: before wait\n");
        wait();
        printf("MSC: unblocked\n");
        RW.blockedReaders--;
        if
        :: RW.curBatch[procId] && RW.writers == 0 -> {
            break;
        };
        :: else -> skip;
        fi;
    }
    :: else -> break;
    od;

    if
    :: RW.blockedReaders > 0 -> {
        notifyAll();
    }
    :: else -> skip;
    fi;
    /* Разблокируем всех ожидающих читателей. Ждём, пока количество заблокированных читателей не станет 0 */
    printf("MSC: blocked readers: %d\n", RW.blockedReaders);

    RW.readers++;
    printf("MSC: readers - %d\n", RW.readers);
    RW.isBatchWorking = true;
    leaveMon();
}

inline endRead() {
    enterMon();
    RW.readers--;
    printf("MSC: readers - %d\n", RW.readers);
    RW.curBatch[procId] = false;
    endReadI = 0;
    do
    :: RW.curBatch[i] == true -> break;
    :: else -> {
        if
        :: endReadI == (READERS - 1) -> {
            RW.isBatchWorking = false;
            copyArr(RW.nextBatch, RW.curBatch);
            copyArr(emptyArr, RW.nextBatch);
            notifyAll();
            break;
        }
        :: else -> skip;
        fi;
        endReadI++;
    };
    od; 
    endReadI = 0;
    leaveMon();
}

inline startWrite() {
    enterMon();
    printf("MSC: try write\n");
    
    do
    :: (RW.writers != 0 || RW.isBatchWorking) -> 
        wait();
    :: else -> break;
    od;
      
    RW.writers++;
    printf("MSC: writers - %d\n", RW.writers);
    leaveMon();
}

inline endWrite() {
    enterMon();
    RW.writers--;
    printf("MSC: writers - %d\n", RW.writers);
    notifyAll();
    leaveMon();
}

monitor RW;

proctype reader() {
    byte i = 0;
    byte k = 0;
    byte endReadI = 0;

    do
    :: REAL_TRUE -> {
          printf("MSC: in non-cs\n");
    };
    :: true -> {
        i = 0;
        r_start:
        startRead();
        if
        :: RW.writers != 0 ->
            r_in_cs_when_w_already_in_cs: {skip;}
        :: else -> skip;
        fi;
        r_in_cs: printf("MSC: in cs\n");
        endRead();
    };
    od;
}

proctype writer() {
    byte i = 0;
    byte k = 0;
    do
    :: REAL_TRUE -> {
        printf("MSC: in non-cs\n");
    }
    :: true -> {
        i = 0;
        w_start:
        startWrite();
        if
        :: RW.readers != 0 ->
            w_in_cs_when_r_already_in_cs: {skip;}
        :: RW.writers > 1 ->
            w_in_cs_when_w_already_in_cs: {skip;}
        :: else -> skip;
        fi;
        w_in_cs: printf("MSC: in cs\n");
        endWrite();
    };
    od;
}

init {
    atomic {
        int j = 0;
      
        do
        :: (j < READERS) -> {
            run reader();
            j++;
        }
        :: else -> break;
        od;
    
        j = 0;

        do
        :: (j < WRITERS) -> {
            run writer();
            j++;
        }
        :: else -> break;
        od;
    }
}