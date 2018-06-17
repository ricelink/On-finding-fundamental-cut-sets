
#this program aims finding all fundamental cut sets,
#when the spanning tree T in undirected graph G is given 
#Python 3.6
#rongjian liu <rongjliu@foxmail.com>
#Jun/16/2018
#
#Refernece: Saxena, S. (2010). On finding fundamental cut sets. Information Processing Letters, 110(4), 168-170.
import copy
import math
import random
import sys 
import time
from enum import Enum
import types
import string


#define COLOR
class COLOR(Enum):
	WHITE = 1,
	GRAY = 2,
	BLACK = 3

WHITE = COLOR.WHITE
GRAY = COLOR.GRAY
BLACK = COLOR.BLACK
#product a random connected undirected graph G
#when probability p>=ln(N)/N, the all most every random G is connected

#lnN = math.log(N) 
#print(N,random.uniform(0,N))
txtName = "G.txt"
class Matrix_G:
	def __init__(self,N=1):
		self.N     = N
		self.Matrix=[[0 for j in range(N)] for i in range(N) ]
		self.p = math.log(N)/N
	def Print(self):
		print('   ',[i for i in range(self.N)])
		for i in range(self.N):
			print(i,':',self.Matrix[i])
		return 1
	def Print2(self):
		
		a=[]
		for i in range(self.N):
			state = 0
			for j in range(self.N):
				if self.Matrix[j][i]>0:
					state = 1
					break
			a.append(state)
		num=0
		for i in range(len(a)):
			if a[i]>0:
				num=num+1
		print('num=',num,a)
	def product(self):# produce the random adjacent matrix for graph G
		for i in range(self.N):
			for j in range(i+1,self.N):
				r=random.random()
				if  r <= self.p:
					self.Matrix[i][j]=1
					self.Matrix[j][i]=1

	def writetxt(self,txtName = "G.txt"):
		f =open(txtName,"a+")
		#localtime = str(time.time())
		#f.write(localtime)
		str11=''.join('%s' %self.N)
		f.write("\nadjacent matrix is "+str11+"*"+str11+ "\nbegin:\n")
		for i in range(self.N):
			str1=",".join('%s' %id for id in self.Matrix[i])
			f.write(str1)
			f.write('\n')
		f.write('end\n')
		f.close()
		return 1
	def Ifconnected(self):
		label =[0 for i in range(self.N)]
		root = 0
		F = []
		label[root]=1
		for i in range(self.N):
			if self.Matrix[root][i] == 1:
				label[i]=1
				F.append(i)
		while(len(F)>0):
			e = F.pop(0)
			for i in range(self.N):
					if self.Matrix[e][i] > 0:
						if label[i] == 0:
							label[i] = 1
							F.append(i)
		for i in range(self.N):
			if label[i]==0:
				return 0
		return 1

class Vertex:
	def __init__(self,v):
		self.v=v
		self.parent=-1# When parent equal to -1, it means that vertex v have no parent. Only root vertex have no parent
		self.previsit=-1
		self.postvisit=-1
		self.pre=-1
		self.alpha=-1
		self.color=WHITE
		self.descendants=[v] #the descendants in the spanning tree T
	def Print(self):
		print('v=',self.v,'parent=',self.parent,'pre=',self.pre,'alpha=',self.alpha,'previsit=',
			  self.previsit,'postvisit=',self.postvisit)
		print('descendants=',self.descendants)

class Edge:
	def __init__(self,u=-1,v=-1):
		self.u=u
		self.v=v
		self.u2=v
		self.v2=u
	def Print(self):
		print('u=',self.u,'v=',self.v,'u2=',self.u2,'v2=',self.v2)

class graph:
	def __init__(self,N=0):
		self.N = N # the vertex number of graph
		self.root_vertex = 0 #default root is vertex 0
		self.matrix = [[] for i in range(N)]
		self.Matrix = Matrix_G()
		self.edge=[[] for i in range(N)]
		self.vertex=[] #append(Vertex(i))
		self.t1=0 #label for previsit postvisit in vertex
		self.t2=0 #label for pre in vertex
	def initgraph(self,M=Matrix_G()):
		self.matrix=copy.deepcopy(M.Matrix)
		self.Matrix=copy.deepcopy(M)
		for i in range(self.N):
			for j in range(self.N):
				if self.matrix[i][j]!=0:
					self.edge[i].append(j)
		for i in range(self.N):
			self.vertex.append(Vertex(i))
	def Print(self):
		print("adjacent matrix:")
		self.Matrix.Print()
		print('vertex:')
		for i in range(self.N):
			self.vertex[i].Print()
		print('edge:')
		for i in range(self.N):
				print(i,":",self.edge[i])
		
	#recursive callable, sub-program for preprocess
	def subpreprocess(self,F): 
		#print('line145=',F)
		for i in range(len(F)):
			e=F[i]
			FF=[]
			self.vertex[e].previsit = self.t1
			self.t1=self.t1+1
			self.vertex[e].pre = self.t2
			self.t2 = self.t2+1
			self.vertex[e].color = BLACK
			for i in range(len(self.edge[e])):
				if self.vertex[self.edge[e][i]].color == WHITE and self.vertex[self.edge[e][i]].parent == -1:
					FF.append(self.edge[e][i])
					self.vertex[self.edge[e][i]].parent = e
			for i in range(len(FF)): 
				self.vertex[e].descendants.append(FF[i]) #the descendants of vertex e
			self.subpreprocess(FF) #the spanning tree is embedded in this function
			self.vertex[e].postvisit = self.t1
			self.t1=self.t1+1


		#label every vertex in graph, previsit time and postvisit time for every vertex in tree T
	def preprocess(self):
		
		F=[]
		#F.append(self.root_vertex)
		self.vertex[self.root_vertex].previsit = self.t1
		self.t1 = self.t1+1
		self.vertex[self.root_vertex].pre = self.t2
		self.t2 = self.t2+1
		self.vertex[self.root_vertex].color = BLACK
		for i in range(len(self.edge[self.root_vertex])):
			if self.vertex[self.edge[self.root_vertex][i]].color == WHITE:
				F.append(self.edge[self.root_vertex][i])
				self.vertex[self.edge[self.root_vertex][i]].parent=self.root_vertex
		for i in range(len(F)): 
			self.vertex[self.root_vertex].descendants.append(F[i]) #the descendants of root vertex 
		self.subpreprocess(F)
		self.vertex[self.root_vertex].postvisit=self.t1
	def alphaprocess(self):#produce \alpha(v) in Refernece Saxena, S. (2010).
		for i in range(self.N):
			self.vertex[i].alpha=int((self.vertex[i].postvisit-self.vertex[i].previsit-1)/2)+self.vertex[i].pre
	
#section Algorithm in Refernece Saxena, S. (2010).
def fundmentalcutsets(G):
	N = G.N # the vertex number of graph G
	vertex = G.vertex
	edge = G.edge
	S=[[] for i in range(N)]
	for v in range(N):
		if vertex[v].parent!=-1:  #vertex[v].parent!=-1 means the vertex v has a parent 
			Aprev = vertex[v].pre
			Aalphv = vertex[v].alpha
			descendants=vertex[v].descendants #list A[i,j] in paper
			for subv in range(len(descendants)):
				dubug1=descendants[subv]
				dubug2=edge[descendants[subv]]
				for u in range(len(edge[descendants[subv]])):
					debug3=vertex[edge[descendants[subv]][u]]
					if vertex[edge[descendants[subv]][u]].pre < Aprev or vertex[edge[descendants[subv]][u]].pre> Aalphv:
						S[v].append(Edge(vertex[edge[descendants[subv]][u]].v,descendants[subv]))
			# for w in range(Aprev, Aalphv+1):
				# for u in range(len(edge[w])):
					# if vertex[edge[w][u]].pre < Aprev or vertex[edge[w][u]].pre> Aalphv:
						# S[v].append(Edge(edge[w][u],v))
	return S

def main(N=1,p=0):
	Gmatrix = Matrix_G(N)
	Gmatrix.p=p
	while(True):#ensure that the graph G is connected
		temp = Matrix_G(N)
		temp.p=p
		temp.product() 
		if temp.Ifconnected():
			Gmatrix.Matrix = copy.deepcopy(temp.Matrix)
			Gmatrix.writetxt()
			break
	G = graph(N)
	G.initgraph(Gmatrix) 
	G.preprocess()
	G.alphaprocess()
	S=fundmentalcutsets(G)
	f =open(txtName,"a+")
	f.write("\nthe fundmental cut sets are: \nbegin \nthe root vertex is "+str(G.root_vertex)+'.\n')
	for i in range(len(S)):
		SI = S[i]
		# print(type(SI))
		# str1=str(i)
		if G.vertex[i].parent==-1:
			continue
		else:
			f.write('for edge ('+str(i)+','+str(G.vertex[i].parent)+'), there exist(s) '+str(len(SI))+' edge(s) need to be removed\n')
		for jj in range(len(SI)):
			f.write('('+str(SI[jj].u)+','+str(SI[jj].v)+') ')
		if G.vertex[i].parent!=-1:
			f.write('\n')
	f.write('end\n')
	f.close()


N = 500#the vertex number of graph G
p=math.log(N)/N #when probability p>=ln(N)/N, the all most every random G is connected

#p=min(p*1.2,1)
# p=1
start=time.time()
main(N,p)
end=time.time()
print('p=',p,'N=',N,'cost time =',end-start,'s')
f =open(txtName,"a+")
f.write('\np='+str(p)+' N='+str(N)+' the runtime is '+str(end-start)+'s\n')
f.close()