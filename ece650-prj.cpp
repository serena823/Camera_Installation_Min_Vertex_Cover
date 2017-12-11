// defined unique_ptr
#include <memory>
// defines Var and Lit
#include "minisat/simp/SimpSolver.h"
// defines Solver
#include "minisat/simp/SimpSolver.h"
#include <vector>
// defined cout
#include <iostream>
#include <algorithm>
#include <string>
#include <sstream>
#include <fstream>
#include <unistd.h>
#include <thread>
#include <pthread.h>
#include <time.h>
#include <iomanip>
using namespace std;

#define handle_error(msg) \
               do { perror(msg); exit(EXIT_FAILURE); } while (0)
#define handle_error_en(en, msg) \
               do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)
int num_var;
bool res;
pthread_mutex_t lockp;

vector<int> min_vc1;
vector<int> min_vc2;
vector<int> result;
vector<int> edge;
int random(int limit){
	ifstream urandom("/dev/urandom");
	int ch = 1;
	urandom.read((char *) &ch, 1);
	urandom.close();
	int rand = ch % limit ;
	if(rand%2 != 0){rand = rand -1; }
	return rand;
}
bool Isseperatpr(char c)
{
    switch(c)
    {
    case '<':
    case '>':
    case '{':
    case '}':
    case ',':

        return true;
    default:
        return false;
    }
}

void map(vector<int>ex){
     int size_ex = ex.size();
    for (int m=0;m<size_ex;m++){
         if(m==size_ex -1){cout<<ex[m];}
        else{cout<<ex[m]<<",";}
        }  
cout<<endl;
}
void update_v(string po_E)
{
  edge.clear();
   string number ;
   for(char i : po_E) {
    if (Isseperatpr(i)== false){
        string I(1,i);
        number = number+I;
    }
    else{
        int result = atoi(number.c_str());
        if(!number.empty()){
        edge.push_back(result);
        number.clear();
        }
    }
   }
}


static void
       pclock(char *msg, clockid_t cid)
       {   pthread_mutex_lock(&lockp);
           struct timespec ts;

           printf("%s", msg);
           if (clock_gettime(cid, &ts) == -1)
               handle_error("clock_gettime");
           printf("%4ld.%06ld\n", ts.tv_sec, ts.tv_nsec / 1000);
           pthread_mutex_unlock(&lockp);
       }


int mode (vector<int> e){

vector<int> histogram(num_var,0);
vector<int>::iterator it = e.begin();
while(it != e.end())    histogram[*it++]++;
return max_element( histogram.begin(), histogram.end() ) - histogram.begin();
}


static void *VC_1(void *arg){

clockid_t cid;
int s;
vector<int> vc_tem = edge;
min_vc1.clear();
int i = 0;
while(!vc_tem.empty()){
    int modes = mode(vc_tem);
    min_vc1.push_back(modes);
    for(int i = 0 ;i<vc_tem.size();){
    if((vc_tem[i]==modes) || (vc_tem[i+1]==modes)){
        vc_tem.erase(vc_tem.begin()+i,vc_tem.begin()+i+2);
    }
    else{
    i+=2;}
    }
}

 //s = pthread_getcpuclockid(pthread_self(), &cid);
// if (s != 0)
  	//handle_error_en(s, "pthread_getcpuclockid");
 //pclock("vc1 running time", cid);
 
}




static void *VC_2(void *arg){
clockid_t cid;
int s;
vector<int> vc_tem = edge;
min_vc2.clear();

while(!vc_tem.empty()){
    int m = random(vc_tem.size());
      //int m = 0;
    min_vc2.push_back(vc_tem[m]);
    min_vc2.push_back(vc_tem[m+1]);
    int s = min_vc2.size();
    for(int i=0;i<vc_tem.size();){
        if((vc_tem[i]==min_vc2[s-1]) || (vc_tem[i+1]==min_vc2[s-1])||(vc_tem[i+1]==min_vc2[s-2])||(vc_tem[i]==min_vc2[s-2])){
        vc_tem.erase(vc_tem.begin()+i,vc_tem.begin()+i+2);
    }
    else{i+=2;}

   }

}

//s = pthread_getcpuclockid(pthread_self(), &cid);
 //if (s != 0)
  //	handle_error_en(s, "pthread_getcpuclockid");
 //pclock("vc2 running time", cid);

}



vector<int> sort (vector<int> a){
sort(a.begin(),a.end());
return a;
}

void *vertex(void *arg){


//////////////////////////////////////////////////////////////////CNF/////////////////////////////////////////
clockid_t cid;
int s;
unique_ptr<Minisat::Solver> solver(new Minisat::Solver());
    // -- allocate on the heap so that we can reset later if needed

    int k =1;
    while(res==0){
    vector<vector<Minisat::Lit>> var;
    Minisat::Lit b0;
    for(int m=0;m<k;m++){
    vector<Minisat::Lit> temp;
    for(int i=0;i<num_var;i++){

    b0 = Minisat::mkLit(solver->newVar());

    temp.push_back(b0);
    	}
    var.push_back(temp);
    }
/////////////////////////////////////////////////////////////////add_clause step 1 hengzhe////////////////////////////

    for(int a=0;a<k;a++){
	for(int b=0; b<num_var;b++){
 	      for(int c=b+1;c<num_var;c++){
	solver->addClause(~var[a][b],~var[a][c]);
      }
    }
}
/////////////////////////////////////////////////////////////////add_clause step 2 yihang////////////////////////////
   for(int a=0;a<k;a++){
     Minisat::vec<Minisat::Lit> row;
     for(int b=0; b<num_var;b++){
	row.push(var[a][b]);
     }
     solver->addClause(row);
 }
/////////////////////////////////////////////////////////////////add_clause step 3 shuzhe///////////////////////////////
   for(int e=0;e<num_var;e++){
       for(int f=0;f<k;f++){
          for (int g=f+1;g<k;g++){
          solver->addClause(~var[f][e],~var[g][e]);

	  }
	}
}
////////////////////////////////////////////////////////////////add_clause step 4 edge //////////////////////
int size_edge = edge.size();
for(int a=0;a<size_edge;a+=2){
  Minisat::vec<Minisat::Lit> E;
  int start = edge[a];
  int end = edge[a+1];
  for(int b=0;b<k;b++){
  E.push(var[b][end]);
  E.push(var[b][start]);
  }
  solver->addClause(E);

}


  res = solver->solve();

/////////////////////////////////////////////////////////////print matrix////////////////////////////////////////////////
    if(res == 1){    
    for(int a=0;a<k;a++){
	for(int b=0;b<num_var;b++){
             if(Minisat::toInt(solver->modelValue(var[a][b]))== 0){

		 result.push_back(b);
		}
            }
        }
        sort(result.begin(),result.end());
        break;

   }
    if(k==num_var){
      cerr<<"Error: not found vertex cover"<<endl;
       break;
    }
    k=k+1;
    //cout<<k<<endl;
    solver.reset (new Minisat::Solver());
    }
//s = pthread_getcpuclockid(pthread_self(), &cid);
 //if (s != 0)
  //	handle_error_en(s, "pthread_getcpuclockid");
 //pclock("sat running time", cid);

}




void *write(void *arg){

while (!cin.eof()){
              
                string po_E;
		string line;
		getline(cin, line);
		istringstream input(line);
		char commend = 'X';
                
		while (!input.eof()){
                  
                commend = 'X';
			input >> commend;
			if (commend == 'V'){
					input >> num_var;
                                                   
					break;
		       }
                else if (commend == 'E'){
                       input >> po_E;
                       update_v(po_E);
                       break;
                       }

                }
           if(num_var > 0 && edge.size() > 0){
            int s;
	    pthread_t thread[3];
            clockid_t cid;clockid_t aid;  

           s = pthread_create(&thread[0], NULL, VC_1, NULL);
           s = pthread_create(&thread[1], NULL, VC_2, NULL);
           s = pthread_create(&thread[2], NULL, vertex, NULL); 
           pthread_join(thread[0],NULL);
           pthread_join(thread[1],NULL);
           pthread_join(thread[2],NULL);
           //double ratio1 = (double(min_vc1.size()))/result.size();
	   //double ratio2 = (double(min_vc2.size()))/result.size();
	   cout<<"CNF-SAT-VC:"<<" ";
           map(result);
           cout<<"APPROX-VC-1:"<<" ";
           map(sort(min_vc1));
           cout<<"APPROX-VC-2:"<<" ";
           map(sort(min_vc2));
            //cout<<"Approxratio 1 :"<<setprecision(3)<<ratio1<<endl;
            //cout<<"Approxratio 2 :"<<setprecision(3)<<ratio2<<endl;
            edge.clear();
            num_var = 0;
            res = 0;
            result.clear();
            min_vc1.clear();
            min_vc2.clear();   
 	}
             
 }   

}
void *output(void *arg){
double ratio1 = (double(min_vc1.size()))/result.size();
double ratio2 = (double(min_vc2.size()))/result.size();
//cout<<"CNF-SAT-VC:"<<" ";
//map(result);
//cout<<"APPROX-VC-1:"<<" ";
//map(sort(min_vc1));
            //cout<<"APPROX-VC-2:"<<" ";
            //map(sort(min_vc2));
            cout<<"Approxratio 1 :"<<setprecision(3)<<ratio1<<endl;
            cout<<"Approxratio 2 :"<<setprecision(3)<<ratio2<<endl;
            edge.clear();
            num_var = 0;
            res = 0;
            
            result.clear();
            min_vc1.clear();
            min_vc2.clear();

}

 /////////////////////////////////////////////////////////////////////////////
int main(void) {
//freopen ("myfile.txt","w",stdout);
/*for(int z = 1 ; z<11;z++){
for(int x = 3 ; x < 18 ;x += 2){

  cout<<x<<endl;
  stringstream strs;
  strs << x;
  string temp_str = strs.str();

string k_string = " + to_string(k) + ";
pid_t child_pid;
vector<pid_t> kids;
char* arg[2];
arg[0] = (char*)"/home/agurfink/ece650/graphGen/graphGen";
arg[1] = (char*) temp_str.c_str();; //vertex number  = "10"
arg[2] = nullptr;
int rgen[2];
pipe(rgen);
child_pid = fork();
if(child_pid == 0)
{
	dup2(rgen[1],STDOUT_FILENO);
	close(rgen[0]);
	close(rgen[1]);
	execv("/home/agurfink/ece650/graphGen/graphGen", arg);
		return 0;
	}
	else if (child_pid < 0) {
        cerr << "Error: could not fork\n";
        return 1;
    }
dup2(rgen[0],STDIN_FILENO);
close(rgen[1]);
close(rgen[0]);
*/
pthread_t input;

int s;
         s = pthread_create(&input, NULL, write, NULL);
           pthread_join(input,NULL);
          

pthread_exit(NULL);
//fclose (stdout);
return 0;
}

