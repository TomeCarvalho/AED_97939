// AED, 2020/2021
// 97939 - Tomé Lopes Carvalho
// 98359 - Gonçalo Fernandes Machado
// 98157 - Miguel Beirão e Branquinho Oliveira Monteiro
//
// Brute-force solution of the generalized weighted job selection problem
//
// Compile with "cc -Wall -O2 job_selection.c -lm" or equivalent
//
// In the generalized weighted job selection problem we will solve here we have T programming tasks and P programmers.
// Each programming task has a starting date (an integer), an ending date (another integer), and a profit (yet another
// integer). Each programming task can be either left undone or it can be done by a single programmer. At any given
// date each programmer can be either idle or it can be working on a programming task. The goal is to select the
// programming tasks that generate the largest profit.
//
// Things to do:
//   0. (mandatory)
//      Place the student numbers and names at the top of this file.
//   1. (highly recommended)
//      Read and understand this code.
//   2. (mandatory)
//      Solve the problem for each student number of the group and for
//        N=1, 2, ..., as higher as you can get and
//        P=1, 2, ... min(8,N)
//      Present the best profits in a table (one table per student number).
//      Present all execution times in a graph (use a different color for the times of each student number).
//      Draw the solutions for the highest N you were able to do.
//   3. (optional)
//      Ignore the profits (or, what is the same, make all profits equal); what is the largest number of programming
//      tasks that can be done?
//   4. (optional)
//      Count the number of valid task assignments. Calculate and display an histogram of the number of occurrences of
//      each total profit. Does it follow approximately a normal distribution?
//   5. (optional)
//      Try to improve the execution time of the program (use the branch-and-bound technique).
//      Can you use divide and conquer to solve this problem?
//      Can you use dynamic programming to solve this problem?
//   6. (optional)
//      For each problem size, and each student number of the group, generate one million (or more!) valid random
//      assignments and compute the best solution found in this way. Compare these solutions with the ones found in
//      item 2.
//   7. (optional)
//      Surprise us, by doing something more!
//   8. (mandatory)
//      Write a report explaining what you did. Do not forget to put all your code in an appendix.

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <string.h> //para memcpy
#include "elapsed_time.h"

// Random number generator interface (do not change anything in this code section)
// In order to ensure reproducible results on Windows and GNU/Linux, we use a good random number generator, available at
//   https://www-cs-faculty.stanford.edu/~knuth/programs/rng.c
// This file has to be used without any modifications, so we take care of the main function that is there by applying
// some C preprocessor tricks

#define main rng_main  // main gets replaced by rng_main
#ifdef __GNUC__
int rng_main() __attribute__((__unused__));  // gcc will not complain if rnd_main() is not used
#endif
#include "rng.c"
#undef main  // main becomes main again

#define srandom(seed) ran_start((long)seed)  // start the pseudo-random number generator
#define random() ran_arr_next()              // get the next pseudo-random number (0 to 2^30-1)


// problem data (if necessary, add new data fields in the structures; do not change anything else in this code section)
// on the data structures declared below, a comment starting with
// * a I means that the corresponding field is initialized by init_problem()
// * a S means that the corresponding field should be used when trying all possible cases
// * IS means both (part initialized, part used)

#if 1

#define MAX_T 64  // maximum number of programming tasks
#define MAX_P 10  // maximum number of programmers

typedef struct {
    int starting_date;  // I starting date of this task
    int ending_date;    // I ending date of this task
    int profit;         // I the profit if this task is performed
    int assigned_to;    // S current programmer number this task is assigned to (use -1 for no assignment)
} task_t;

typedef struct {
    int NMec;            // I  student number
    int T;               // I  number of tasks
    int P;               // I  number of programmers
    int I;               // I  if 1, ignore profits
    int total_profit;    // S  current total profit
    double cpu_time;     // S  time it took to find the solution
    task_t task[MAX_T];  // IS task data
    int busy[MAX_P];     // S  for each programmer, record until when she/he is busy (-1 means idle)
    char dir_name[16];   // I  directory name where the solution file will be created
    char file_name[64];  // I  file name where the solution data will be stored

    // members adicionados
    int *opt_sol;               // guarda as tasks que levam ao profit máximo
    int *current_sol;           // guarda as tasks da solução atual
    int current_sol_profit;     // profit da solução atual
    int profit_limit;           // para o profit_occurrence_arr, é o limite dos índices do array (soma dos profits de todas as tasks)
    int *profit_occurrence_arr; // guarda o número de vezes que cada profit é calculado
    long unsigned int n_viable_sol;           // número de soluções viáveis (conjuntos de tasks que podem ser feitos)
    char file_name_hist[64];    // nome para os ficheiros do histograma
} problem_t;

int compare_tasks(const void *t1, const void *t2) {
    int d1, d2;

    d1 = ((task_t *)t1)->starting_date;
    d2 = ((task_t *)t2)->starting_date;
    if (d1 != d2)
        return (d1 < d2) ? -1 : +1;
    d1 = ((task_t *)t1)->ending_date;
    d2 = ((task_t *)t2)->ending_date;
    if (d1 != d2)
        return (d1 < d2) ? -1 : +1;
    return 0;
}

void init_problem(int NMec, int T, int P, int ignore_profit, problem_t *problem) {
    int i, r, scale, span, total_span;
    int *weight;


    // input validation
    if (NMec < 1 || NMec > 999999) {
        fprintf(stderr, "Bad NMec (1 <= NMex (%d) <= 999999)\n", NMec);
        exit(1);
    }
    if (T < 1 || T > MAX_T) {
        fprintf(stderr, "Bad T (1 <= T (%d) <= %d)\n", T, MAX_T);
        exit(1);
    }
    if (P < 1 || P > MAX_P) {
        fprintf(stderr, "Bad P (1 <= P (%d) <= %d)\n", P, MAX_P);
        exit(1);
    }

    // the starting and ending dates of each task satisfy 0 <= starting_date <= ending_date <= total_span
    total_span = (10 * T + P - 1) / P;
    if (total_span < 30)
        total_span = 30;

    // probability of each possible task duration
    // task span relative probabilities
    // |  0  0  4  6  8 10 12 14 16 18 | 20 | 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1 | smaller than 1
    // |  0  0  2  3  4  5  6  7  8  9 | 10 | 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 | 30 31 ... span
    //
    weight = (int *)alloca((size_t)(total_span + 1) * sizeof(int));  // allocate memory (freed automatically)
    if (weight == NULL) {
        fprintf(stderr, "Strange! Unable to allocate memory\n");
        exit(1);
    }
#define sum1 (298.0)                      // sum of weight[i] for i=2,...,29 using the data given in the comment above
#define sum2 ((double)(total_span - 29))  // sum of weight[i] for i=30,...,data_span using a weight of 1
#define tail 100
    scale = (int)ceil((double)tail * 10.0 * sum2 / sum1);  // we want that scale*sum1 >= 10*tail*sum2, so that large task
    if (scale < tail)                                      // durations occur 10% of the time
        scale = tail;
    weight[0] = 0;
    weight[1] = 0;
    for (i = 2; i <= 10; i++)
        weight[i] = scale * (2 * i);
    for (i = 11; i <= 29; i++)
        weight[i] = scale * (30 - i);
    for (i = 30; i <= total_span; i++)
        weight[i] = tail;
#undef sum1
#undef sum2
#undef tail

    // accumulate the weights (cummulative distribution)
    for (i = 1; i <= total_span; i++)
        weight[i] += weight[i - 1];

    // generate the random tasks
    srandom(NMec + 314161 * T + 271829 * P);
    problem->NMec = NMec;
    problem->T = T;
    problem->P = P;
    problem->I = (ignore_profit == 0) ? 0 : 1;
    for (i = 0; i < T; i++) {

        // task starting an ending dates
        r = 1 + (int)random() % weight[total_span];  // 1 .. weight[total_span]
        for (span = 0; span < total_span; span++)
            if (r <= weight[span])
                break;
        problem->task[i].starting_date = (int)random() % (total_span - span + 1);
        problem->task[i].ending_date = problem->task[i].starting_date + span - 1;

        // task profit
        // the task profit is given by r*task_span, where r is a random variable in the range 50..300 with a probability
        //   density function with shape (two triangles, the area of the second is 4 times the area of the first)
        //
        //      *
        //     /|   *
        //    / |       *
        //   /  |           *
        //  *---*---------------*
        // 50 100 150 200 250 300

        scale = (int)random() % 12501;  // almost uniformly distributed in 0..12500
        if (scale <= 2500)
            problem->task[i].profit = 1 + round((double)span * (50.0 + sqrt((double)scale)));
        else
            problem->task[i].profit = 1 + round((double)span * (300.0 - 2.0 * sqrt((double)(12500 - scale))));
    }

    // sort the tasks by the starting date
    qsort((void *)&problem->task[0], (size_t)problem->T, sizeof(problem->task[0]), compare_tasks);

    // finish
    if (problem->I != 0)
        for (i = 0; i < problem->T; i++)
            problem->task[i].profit = 1;
#define DIR_NAME problem->dir_name
    if (snprintf(DIR_NAME, sizeof(DIR_NAME), "%06d", NMec) >= sizeof(DIR_NAME)) {
        fprintf(stderr, "Directory name too large!\n");
        exit(1);
    }
#undef DIR_NAME
#define FILE_NAME problem->file_name
    if (snprintf(FILE_NAME, sizeof(FILE_NAME), "%06d/%02d_%02d_%d.txt", NMec, T, P, problem->I) >= sizeof(FILE_NAME)) {
        fprintf(stderr, "File name too large!\n");
        exit(1);
    }
#undef FILE_NAME
#define FILE_NAME_HIST problem->file_name_hist
    if (snprintf(FILE_NAME_HIST, sizeof(FILE_NAME_HIST), "%06d/%02d_%02d_%d_hist.txt", NMec, T, P, problem->I) >= sizeof(FILE_NAME_HIST)) {
        fprintf(stderr, "File name too large!\n");
        exit(1);
    }
#undef FILE_NAME_HIST
}

#endif

// problem solution (place your solution here)
void recursive_sol(problem_t *problem, int t) { // solução recursiva
    if (t == problem->T) {                                  // se estivermos na última task
        problem->n_viable_sol++;                            // encontrámos uma solução viável, incrementar n_viable_sol

        problem->profit_occurrence_arr[problem->current_sol_profit]++;       // incrementar o número de vezes que se calculou este profit

        if (problem->current_sol_profit > problem->total_profit) {
            problem->total_profit = problem->current_sol_profit;
            memcpy(problem->opt_sol, problem->current_sol, problem->T * sizeof(int));
        }

        return;
    }

    // calcular profit excluíndo a task atual
    problem->task[t].assigned_to = -1;  // a task não vai ser feita por ninguém
    recursive_sol(problem, t + 1);      // passar para a próxima task

    // calcular profit incluíndo a task atual
    int p = 0;                                                   // índice do programador que vai fazer a task (1º que estiver disponível)
    //for(; p < problem->P; p++)                                            // percorrer os programadores
    //    if (problem->busy[p] < problem->task[t].starting_date)   // até encontrar um que esteja disponível a tempo de fazer a task
    //       break;                                               // sair do loop porque encontrámos um programador disponível

    while (problem->busy[p] >= problem->task[t].starting_date && p < problem->P)
        p++;    // percorrer programadores até encontrar o primeiro disponível ou até ter percorrido todos (p == P)

    // O while demonstra ser igual
    //
    if (p < problem->P) {                                            // se p == P, não havia nenhum programador disponível
        int tmp_busy = problem->busy[p];                         // guardar o busy state do programador que vai fazer a task
        int tmp_profit = problem->current_sol_profit;
        //int tmp_do_task = problem->current_sol[t];

        problem->busy[p] = problem->task[t].ending_date;    // uma vez que é alterado nesta linha
        problem->task[t].assigned_to = p;                   // alterar também o assigned_to da task
        problem->current_sol_profit += problem->task[t].profit;
        problem->current_sol[t] = 1;
        recursive_sol(problem, t + 1);                      // passar para a próxima task

        problem->busy[p] = tmp_busy;                             // restaurar o estado do busy para o programador
        problem->current_sol_profit = tmp_profit;
        problem->current_sol[t] = 0;
    }
}

void solution(problem_t *problem) {
    // inicializar os members adicionados à struct problem_t
    problem->n_viable_sol = 0;
    problem->current_sol_profit = 0;
    problem->total_profit = 0;
    problem->profit_limit = 0;

    problem->current_sol = (int *) malloc(problem->T * sizeof(int));
    problem->opt_sol = (int *) malloc(problem->T * sizeof(int));

    // equivalente ao Arrays.fill(this.busy, -1) do Java
    for (int i = 0; i < problem->P; i++)
        problem->busy[i] = -1;

    for (int i = 0; i < problem->T; i++) {
        problem->profit_limit += problem->task[i].profit; // calcular o limite de profit
        problem->current_sol[i] = 0;                      // inicializar current_sol a zeros
    }

    problem->profit_occurrence_arr = (int *) malloc(problem->profit_limit * sizeof(int)); // alocar memória para o profit_occurrence_arr de acordo com o limite de profit

    recursive_sol(problem, 0); // chamar a função recursiva que resolve o problema
}

#if 1

static void solve(problem_t *problem) {
    FILE *fp;
    FILE *hist;
    int i;

    // open log file
    (void)mkdir(problem->dir_name, S_IRUSR | S_IWUSR | S_IXUSR);
    fp = fopen(problem->file_name, "w");
    if (fp == NULL) {
        fprintf(stderr, "Unable to create file %s (maybe it already exists? If so, delete it!)\n", problem->file_name);
        exit(1);
    }

    // solve
    problem->cpu_time = cpu_time();
    // call your (recursive?) function to solve the problem here
    solution(problem);
    //
    problem->cpu_time = cpu_time() - problem->cpu_time;

    // save solution data
    fprintf(fp, "NMec = %d\n", problem->NMec);
    fprintf(fp, "T = %d\n", problem->T);
    fprintf(fp, "P = %d\n", problem->P);
    fprintf(fp, "Profits%s ignored\n", (problem->I == 0) ? " not" : "");
    fprintf(fp, "Solution time = %.6e\n", problem->cpu_time);

    // custom
    fprintf(fp, "Max Profit = %d\n", problem->total_profit);
    fprintf(fp, "Number of viable task sets = %lu\n", problem->n_viable_sol);
    //

    //fprintf(fp, "Task data\n");
    fprintf(fp, "Task data (number, starting date, ending date, profit, done in optimal solution)\n");
#define TASK problem->task[i]
    for (i = 0; i < problem->T; i++)
        //fprintf(fp, "  %3d %3d %5d\n", TASK.starting_date, TASK.ending_date, TASK.profit);
        fprintf(fp, "  %3d %3d %3d %5d %3d\n", i, TASK.starting_date, TASK.ending_date, TASK.profit, problem->opt_sol[i]);
#undef TASK
    fprintf(fp, "End\n");

    // terminate
    if (fflush(fp) != 0 || ferror(fp) != 0 || fclose(fp) != 0) {
        fprintf(stderr, "Error while writing data to file %s\n", problem->file_name);
        exit(1);
    }

    // hist = fopen(problem->file_name_hist, "w");
    // for(i = 0; i <= problem->profit_limit; i++){
    //     if(problem->profit_occurrence_arr[i] != 0){
    //         fprintf(hist, "%2d %4d\n",i ,problem->profit_occurrence_arr[i]);
    //     }
    // }

    // // terminate
    // if (fflush(hist) != 0 || ferror(hist) != 0 || fclose(hist) != 0) {
    //     fprintf(stderr, "Error while writing data to file %s\n", problem->file_name_hist);
    //     exit(1);
    // }
}

#endif


// main program
int main(int argc, char **argv) {
    problem_t problem;
    int NMec, T, P, I;

    // variáveis usadas para calcular a diferença na velocidade entre o for e o while
    // int n = 0;
    // double ave_time = 0;

    // int nmec[3] = {97939, 98157, 98359};    // array para correr o programa pelos 3 nmec
    // int nmec[1] = {98157};

    // ciclos for para correr todas as variações desejadas do programa

    // for(int i = 0; i < 3; i++){
    //    for(T = 1; T <= 35; T++){
    //        for(P = 1; P <= 8; P++){
    //            for(I = 0; I <= 1; I++){
    //                init_problem(nmec[i], T, P, I, &problem);
    //                solve(&problem);
    //            }
    //        }
    //    }
    // }

    // Código original que corre só 1 caso
    NMec = (argc < 2) ? 2020 : atoi(argv[1]);
    T = (argc < 3) ? 5 : atoi(argv[2]);
    P = (argc < 4) ? 2 : atoi(argv[3]);
    I = (argc < 5) ? 0 : atoi(argv[4]);

    // ave_time = cpu_time();    // marca o ínicio das experiências
    // while(n<1000){
       init_problem(NMec, T, P, I, &problem);
       solve(&problem);
    //    n ++;
    // }

    // ave_time = cpu_time() - ave_time; // marca o fim das experiências
    // printf("Average time: %5.5e\n", ave_time);   // mostra o tempo total que as esperiências demoraram

    return 0;
}