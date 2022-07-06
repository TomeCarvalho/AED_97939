//
// AED, 2020/2021
//
// Decoding a non-instantaneous binary code
//

#include <stdio.h>
#include <stdlib.h>


//
// Compile time parameters
//

#ifndef MAX_N_SYMBOLS
# define MAX_N_SYMBOLS         100 // maximum number of alphabet symbols in a code
#endif
#ifndef MAX_CODEWORD_SIZE
# define MAX_CODEWORD_SIZE      23 // maximum number of bits of a codeword
#endif
#ifndef MAX_MESSAGE_SIZE
# define MAX_MESSAGE_SIZE   100000 // maximum number of symbols in a message
#endif

#ifndef N_OUTLIERS
# define N_OUTLIERS             20 // discard this number of mesurements (outliers) on each side of the median
#endif
#ifndef N_VALID
# define N_VALID                80 // use this number of measurements on each side of the median
#endif
#define N_MEASUREMENTS  (2 * N_OUTLIERS + 2 * N_VALID + 1)  // total number of measurements


//
// Random number generator interface
//
// In order to ensure reproducible results on Windows and GNU/Linux, we use a good random number generator, available at
//   https://www-cs-faculty.stanford.edu/~knuth/programs/rng.c
// This file has to be used without any modifications, so we take care of the main function that is there by applying
// some C preprocessor tricks
//
// DO NOT CHANGE THIS CODE
//

#define main  rng_main                        // main gets replaced by rng_main
#ifdef __GNUC__
int rng_main() __attribute__((__unused__));   // gcc will not complain if rnd_main() is not used
#endif
#include "rng.c"
#undef main                                   // main becomes main again

#define srandom(seed)  ran_start((long)seed)  // start the pseudo-random number generator
#define random()       ran_arr_next()         // get the next pseudo-random number (0 to 2^30-1)


//
// Generation of a random non-instantaneous uniquely decodable code with n symbols (inverted Hufffman code)
//
// DO NOT CHANGE THIS CODE
//

typedef struct
{
  int scaled_prob;                      // proportional to the probability of occurrence of this symbol
  int cum_scaled_prob;                  // proportional to the probability of occurrence of this or of all previous symbols
  int parent;                           // -1 means no parent, >= 0 gives the index of the parent
  int bit;                              // -1 means no information, 0 or 1 means append this bit to the parent's code
  char codeword[MAX_CODEWORD_SIZE + 1]; // the complete (inverted) Huffman code
}
symbol_t;

typedef struct
{
  int n_symbols;    // the number of symbols
  int max_bits;     // maximum number of bits of a codeword
  symbol_t *data;   // the symbols and their codes (with extra data at the end --- used to construct the entire Huffman tree)
}
code_t;

void free_code(code_t *c)
{
  if(c != NULL)
  {
    if(c->data != NULL)
      free(c->data);
    c->data = NULL;
    free(c);
  }
}

code_t *new_code(int n_symbols)
{
  int i,i0,i1,n;
  code_t *c;

  //
  // Refuse to handle too few or too many symbols
  //
  if(n_symbols < 2 || n_symbols > MAX_N_SYMBOLS)
  {
    fprintf(stderr,"new_code: n_symbols (%d) is either too small or too large\n",n_symbols);
    exit(1);
  }
  //
  // Allocate memory for the n_symbols symbols plus n_symbols-1 tree nodes for the Huffman tree
  //
  c = (code_t *)malloc(sizeof(code_t));
  if(c == NULL)
  {
    fprintf(stderr,"new_code: out of memory\n");
    exit(1);
  }
  c->data = (symbol_t *)malloc((size_t)(2 * n_symbols - 1) * sizeof(symbol_t));
  if(c->data == NULL)
  {
    free(c);
    fprintf(stderr,"new_code: out of memory\n");
    exit(1);
  }
  //
  // Initialize the symbols --- at the beginning, the symbols (leaves of the Huffman tree) are disconnected
  //
  c->n_symbols = n_symbols;
  for(i = 0;i < n_symbols;i++)
  {
    c->data[i].scaled_prob = 10 + (int)random() % 991;              // a pseudo-random integer belonging to the interval [10,1000]
    c->data[i].cum_scaled_prob = c->data[i].scaled_prob;            // used only to generate
    if(i > 0)                                                       //   symbols with the
      c->data[i].cum_scaled_prob += c->data[i - 1].cum_scaled_prob; //   correct probability
    c->data[i].parent = -1;                                         // currently, no parent node
    c->data[i].bit = -1;                                            // currently, no bit numbier
    c->data[i].codeword[0] = '\0';                                  // currently, no codeword string
  }
  //
  // Construct the Huffman code
  //
  // We are going to do it in a O(n^2) way --- speed is not important here
  // Using min-heaps would reduce that to O(n log n), but the code would be longer and more difficult to understand
  //
  n = n_symbols;
  for(;;)
  {
    //
    // Find the two "open" nodes (those with a parent equal to -1) with the smallest scaled_prob
    //
    i0 = i1 = -1;
    for(i = 0;i < n;i++)
      if(c->data[i].parent == -1)
      { // ok, we have an open node
        if(i0 < 0 || c->data[i].scaled_prob < c->data[i0].scaled_prob)
        { // the smallest scaled_prob so far
          i1 = i0;
          i0 = i;
        }
        else if(i1 < 0 || c->data[i].scaled_prob < c->data[i1].scaled_prob)
        { // the second smallest scaled_prob so far
          i1 = i;
        }
      }
    //
    // Are we done? Yes when we cannot find two open nodes (this will happen when n == 2 * n_symbols - 1)
    //
    if(i1 < 0)
      break;
    //
    // Merge the two open nodes (close them and create a new open node)
    //
    c->data[n].scaled_prob = c->data[i0].scaled_prob + c->data[i1].scaled_prob;
    c->data[n].cum_scaled_prob = -1; // not used but we initialize it anyway
    c->data[n].parent = -1;
    c->data[n].bit = -1;
    c->data[n].codeword[0] = '\0';   // not used but we initialize it anyway
    c->data[i0].parent = n;          // the parent of node i0 becomes node n --- the left descendant of node n is node i0 (we do not record this information)
    c->data[i0].bit = 0;             // give this branch a bit of 0
    c->data[i1].parent = n;          // the parent of node i1 becomes node n --- the right descendant of node n is node i1 (we do not record this information)
    c->data[i1].bit = 1;             // give this branch a bit of 1
    n++;
  }
  if(n != 2 * n_symbols - 1)
  {
    fprintf(stderr,"new_code: unexpected value of n [expected %d, we got %d]\n",2 * n_symbols - 1,n);
    exit(1);
  }
  //
  // For each symbol, initialize its (inverted) Huffman code
  //
  c->max_bits = 0;
  for(n = 0;n < n_symbols;n++)
  {
    i = 0;  // the current code size
    i0 = n; // the initial tree node index
    while(c->data[i0].parent >= 0)
    {
      if(i >= MAX_CODEWORD_SIZE)
      {
        fprintf(stderr,"ne_code: MAX_CODEWORD_SIZE is too small\n");
        exit(1);
      }
      c->data[n].codeword[i] = '0' + c->data[i0].bit;
      i++;
      i0 = c->data[i0].parent;
    }
    c->data[n].codeword[i] = '\0'; // terminate the codeword string
    if(i > c->max_bits)
      c->max_bits = i;
  }
  //
  // Done!
  //
  return c;
}


//
// Random code symbol
//
// DO NOT CHANGE THIS CODE
//

int random_symbol(code_t *c)
{
  int i,r;

  //
  // Generate an (approximately) uniformly distributed integer in the appropriate range
  //
  r = random() % c->data[c->n_symbols - 1].cum_scaled_prob;
  //
  // Find the index i for which c->data[i - 1].cum_scaled_prob <= r < c->data[i].cum_scaled_prob (with c->data[-1].cum_scaled_prob implicitly 0)
  // We are going to do it in a O(n) way --- speed is not important here
  // We could have used a special version of binary search here, but the code would be longer and more difficult to understand
  //
  for(i = 0;i < c->n_symbols;i++)
    if(r < c->data[i].cum_scaled_prob)
      break;
  if(i == c->n_symbols)
  {
    fprintf(stderr,"ramdom_symbol: i is too large! Impossible!!! [r=%d]\n",r);
    exit(1);
  }
  return i;
}


//
// Random message
//
// DO NOT CHANGE THIS CODE
//

void random_message(code_t *c,int message_size,int message[message_size])
{
  int i;

  if(message_size < 1 || message_size > MAX_MESSAGE_SIZE)
  {
    fprintf(stderr,"random_message: bad message size (%d)\n",message_size);
    exit(1);
  }
  for(i = 0;i < message_size;i++)
    message[i] = random_symbol(c);
}


//
// Encode a message
//
// DO NOT CHANGE THIS CODE
//

void encode_message(code_t *c,int message_size,int message[message_size],int max_encoded_message_size,char encoded_message[max_encoded_message_size + 1])
{
  int i,j,n;
  char *s;

  if(message_size < 1 || message_size > MAX_MESSAGE_SIZE)
  {
    fprintf(stderr,"encode_message: bad message size (%d)\n",message_size);
    exit(1);
  }
  n = 0; // encoded message size
  for(i = 0;i < message_size;i++)
  {
    if(message[i] < 0 || message[i] >= c->n_symbols)
    {
      fprintf(stderr,"encoded_message: unexpected symbol (%d)\n",message[i]);
      exit(1);
    }
    s = c->data[message[i]].codeword;
    for(j = 0;s[j] != 0;j++)
    {
      if(n > max_encoded_message_size)
      {
        fprintf(stderr,"encode_message: the encoded message is too big\n");
        exit(1);
      }
      encoded_message[n++] = s[j]; // concatenate the code word
    }
  }
  encoded_message[n] = '\0'; // terminate the string
}


//
// Global data used for decoding (to avoid passing all this information in function arguments, thus making the program more efficient)
//

struct
{
  code_t * c;                        // the code being used
  int    * original_message;         // the original message
  int      original_message_size;    // the original message length
  int      max_encoded_message_size; // the largest possible encoded message size
  char   * encoded_message;          // the encoded message
  int      max_decoded_message_size; // the largest possible decoded message length
  int    * decoded_message;          // the decoded message (should be equal to the original message)
  long     number_of_calls;          // the number of recursive function calls
  long     number_of_solutions;      // the number of solutions (at the end, is all is well, must be equal to 1)
  int      max_extra_symbols;        // the largest difference between the partially decoded message and the good part of the partially decoded message)
}
decoder_global_data;

#define _c_                         decoder_global_data.c
#define _original_message_          decoder_global_data.original_message
#define _original_message_size_     decoder_global_data.original_message_size
#define _max_encoded_message_size_  decoder_global_data.max_encoded_message_size
#define _encoded_message_           decoder_global_data.encoded_message
#define _max_decoded_message_size_  decoder_global_data.max_decoded_message_size
#define _decoded_message_           decoder_global_data.decoded_message
#define _number_of_calls_           decoder_global_data.number_of_calls
#define _number_of_solutions_       decoder_global_data.number_of_solutions
#define _max_extra_symbols_         decoder_global_data.max_extra_symbols


//
// Recursive decoder
//
// encoded_idx ......... index into the _encoded_message_ array of the next bit to be considered
// decoded_idx ......... index into the _decoded_message_ array where the next decoded symbol will be placed
// good_decoded_size ... number of correct decoded symbols
//
// Decoding large messages require a large amount of stack space (one recursion level per message symbol)
// If you get a segmentation fault in our program you may need to increase the stack size (under GNU/linux, you can do it using the command "ulimit -s 16384")
//

static void recursive_decoder(int encoded_idx, int decoded_idx, int good_decoded_size) {
  _number_of_calls_++; // incrementar número de calls da função feitas
  if (_encoded_message_[encoded_idx] == '\0') { // se tivermos descodificado tudo (corretamente, já que não é ambíguo)
    _number_of_solutions_++;
    return;
  }
  // fazer decoded_idx - good_decoded_size, diz-nos o número de símbolos extra que estão mal
  // comparamos a diferença com o max_extra_symbols, se for maior, atualizar max_extra_symbols
  int wrong_symbols = decoded_idx - good_decoded_size;
  if (wrong_symbols > _max_extra_symbols_)
    _max_extra_symbols_ = wrong_symbols;
  
  for (int i = 0; i < _c_->n_symbols; i++) { // para cada símbolo/codeword
    int possible = 1; // flag que indica se é possível ser este símbolo o próximo
    int j = 0;        // índice do caractere da codeword do símbolo
    // comparar a codeword com a enconded message "bit a bit"
    while (_c_->data[i].codeword[j] != '\0') {                // enquanto não tiver acabado a codeword
      // verificar se o caractere atual coincide com o da encoded message
      if (_c_->data[i].codeword[j] != _encoded_message_[encoded_idx + j]) {
        possible = 0; // se for diferente, é impossível ser este símbolo
        break; 
      }
      j++;
    }
    
    if (possible) { // se puder ser este símbolo
      if (good_decoded_size == decoded_idx && i == _original_message_[good_decoded_size]) { // se for o símbolo correto (o que está na mensagem original)
        _decoded_message_[decoded_idx] = i; // atualizar a decoded message
        // int k = 0;
        // while (_decoded_message_[k] != '\0')
        //   printf("%d ", _decoded_message_[k++]);
        // printf("\n");
        recursive_decoder(encoded_idx + j, decoded_idx + 1, good_decoded_size + 1); // chamada quando estamos no caminho correto
      }
      else { // se estivermos no caminho errado (sabemos porque fazemos "batota")                                            
        recursive_decoder(encoded_idx + j, decoded_idx + 1, good_decoded_size); // não chamar com good_decoded_size incrementado
      }
    }
  }
}


//
// Encode and decode driver
//
// DO NOT CHANGE THIS CODE
//

void try_it(code_t *c,int message_size,int show_results)
{
  if(message_size < 1 || message_size > MAX_MESSAGE_SIZE)
  {
    fprintf(stderr,"try_it: bad message size (%d)\n",message_size);
    exit(1);
  }
  _c_ = c;
  _original_message_size_ = message_size;
  _max_encoded_message_size_ = message_size * c->max_bits;
  _max_decoded_message_size_ = message_size + 2000;
  _original_message_ = (int *)malloc((size_t)_original_message_size_ * sizeof(int));
  _encoded_message_ = (char *)malloc((size_t)(_max_encoded_message_size_ + 1) * sizeof(char));
  _decoded_message_ = (int *)malloc((size_t)_max_decoded_message_size_ * sizeof(int));
  _number_of_calls_ = 0L;
  _number_of_solutions_ = 0L;
  _max_extra_symbols_ = -1;
  if(_original_message_ == NULL || _encoded_message_ == NULL || _decoded_message_ == NULL)
  {
    fprintf(stderr,"try it: out of memory!\n");
    exit(1);
  }
  random_message(_c_,_original_message_size_,_original_message_);
  encode_message(_c_,_original_message_size_,_original_message_,_max_encoded_message_size_,_encoded_message_);
  recursive_decoder(0,0,0);
  if(_number_of_solutions_ != 1L)
  {
    fprintf(stderr,"number of solutions: %ld\n",_number_of_solutions_);
    fprintf(stderr,"number of function calls: %ld (%.3f per message symbol)\n",_number_of_calls_,(double)_number_of_calls_ / (double)_original_message_size_);
    fprintf(stderr,"number of extra symbols: %d\n",_max_extra_symbols_);
  }
  if(show_results != 0)
  {
    //
    // print some data about this particular case (average number of calls per symbol, worst probe lookahead)
    //
    printf("%4d %9.3f %3d\n",_c_->n_symbols,(double)_number_of_calls_ / (double)_original_message_size_,_max_extra_symbols_);
    fflush(stdout);
  }
  free(_original_message_); _original_message_ = NULL;
  free(_encoded_message_);  _encoded_message_  = NULL;
  free(_decoded_message_);  _decoded_message_  = NULL;
}


//
// Main program
//
// DO NOT CHANGE THIS CODE
//

int main(int argc,char **argv)
{
  //
  // Show code words (called with arguments -s n_symbols seed)
  //
  if(argc == 4 && argv[1][0] == '-' && argv[1][1] == 's')
  {
    int seed,n_symbols,i;
    code_t *c;

    n_symbols = atoi(argv[2]);
    seed = atoi(argv[3]);
    srandom(seed);
    c = new_code(n_symbols);
    printf("seed: %d\n",seed);
    printf("number of symbols: %d\n",c->n_symbols);
    printf("maximum bits of a code word: %d\n\n",c->max_bits);
    printf("symb freq  cfreq codeword\n");
    printf("---- ---- ------ --------------------\n");
    for(i = 0;i < c->n_symbols;i++)
      printf("%4d %4d %6d %s\n",i,c->data[i].scaled_prob,c->data[i].cum_scaled_prob,c->data[i].codeword);
    printf("---- ---- ------ --------------------\n\n");
    free_code(c);
    return 0;
  }
  //
  // Encode and decode a message (called with arguments -t [n_symbols [message_size [seed]]])
  //
  if(argc >= 2 && argc <= 5 && argv[1][0] == '-' && argv[1][1] == 't')
  {
    int n_symbols,message_size,seed;
    code_t *c;

    n_symbols = (argc < 3) ? 3 : atoi(argv[2]);
    message_size = (argc < 4) ? 10 : atoi(argv[3]);
    seed = (argc < 5) ? 1 : atoi(argv[4]);
    srandom(seed);
    c = new_code(n_symbols);
    try_it(c,message_size,1);
    free_code(c);
    return 0;
  }
  //
  // Try the first N_MEASUREMENTS seeds (called with arguments -x n_symbols)
  //
  if(argc == 3 && argv[1][0] == '-' && argv[1][1] == 'x')
  {
    double t,t_min,t_max,t_avg,t_data[N_MEASUREMENTS],u_avg;
    int u,u_min,u_max,u_data[N_MEASUREMENTS];
    int seed,n_symbols,i;
    code_t *c;

    n_symbols = atoi(argv[2]);
    if(n_symbols == 2)
    {
      printf("# data for MAX_MESSAGE_SIZE equal to %d\n",MAX_MESSAGE_SIZE);
      printf("# data for N_OUTLIERS equal to %d\n",N_OUTLIERS);
      printf("# data for N_VALID equal to %d\n",N_VALID);
      printf("#\n");
      printf("#      number of calls per message symbol      lookahead symbols\n");
      printf("#     -----------------------------------  ---------------------\n");
      printf("# ns       min      avg      med      max   min    avg  med  max\n");
      printf("#---  -------- -------- -------- --------  ---- ------ ---- ----\n");
    }
    if(n_symbols < 3 || n_symbols > MAX_N_SYMBOLS)
    {
      fprintf(stderr,"main: bad number of symbols for the -x command line option\n");
      exit(1);
    }
    t_min = t_max = 0.0;
    u_min = u_max = 0;
    for(seed = 1;seed <= N_MEASUREMENTS;seed++)
    {
      srandom(seed);
      c = new_code(n_symbols);
      try_it(c,MAX_MESSAGE_SIZE,0);
      free_code(c);
      t = (double)_number_of_calls_ / (double)MAX_MESSAGE_SIZE;
      u = _max_extra_symbols_;
      if(seed == 1 || t < t_min)
        t_min  = t;
      if(seed == 1 || t > t_max)
        t_max  = t;
      if(seed == 1 || u < u_min)
        u_min  = u;
      if(seed == 1 || u > u_max)
        u_max  = u;
      for(i = seed - 1;i > 0 && t_data[i - 1] > t;i--) // inner loop of insertion sort!
        t_data[i] = t_data[i - 1];
      t_data[i] = t;
      for(i = seed - 1;i > 0 && u_data[i - 1] > u;i--) // inner loop of insertion sort!
        u_data[i] = u_data[i - 1];
      u_data[i] = u;
    }
    t_avg = u_avg = 0.0;
    for(i = N_OUTLIERS;i < N_MEASUREMENTS - N_OUTLIERS;i++)
    {
      t_avg += t_data[i];
      u_avg += (double)u_data[i];
    }
    t_avg /= (double)(2 * N_VALID + 1);
    u_avg /= (double)(2 * N_VALID + 1);
    printf("%4d  %8.3f %8.3f %8.3f %8.3f  %4d %6.1f %4d %4d\n",n_symbols,t_min,t_avg,t_data[N_OUTLIERS + N_VALID],t_max,u_min,u_avg,u_data[N_OUTLIERS + N_VALID],u_max);
    return 0;
  }
  //
  // Help message
  //
  fprintf(stderr,"usage: %s -s n_symbols seed                     # show the code words of random code\n",argv[0]);
  fprintf(stderr,"       %s -t [n_symbols [message_size [seed]]]  # encode and decode a message\n",argv[0]);
  fprintf(stderr,"       %s -x n_symbols                          # try the first %d seeds\n",argv[0],N_MEASUREMENTS);
  return 1;
}