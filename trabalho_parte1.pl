
:-op(900,xfy,'::').
:-op(900, xfy, 'e').
:-op(900, xfy, 'ou').
:-dynamic('-'/1).
:-dynamic('.'/1).
:-dynamic('+'/1).
:-dynamic(utente/5).
:-dynamic(registo/9).
:-dynamic(imc/6).


%------------------------------------------------------------------------------------------------
% PREDICADOS
%------------------------------------------------------------------------------------------------
% Extensão do predicado utente: Numero_do_utente,Nome,Cidade,Sexo,Antecedentes_familiares ↝ {V,F,D}                           Numero_do_utente começa 1,2,3,...; Antecedentes_familiares é "sim" ou "nao" 
% Extensão do predicado registo: Registo,Numero_do_utente,Dia,Mes,Ano,Idade,Altura(em cm),Peso,Tipo_de_dieta ↝ {V,F,D}       no Tipo_de_dieta, é dizer se é "boa" ou "ma"; n Registo, vamos criar um numero a toa, cada registo vai ter um número associado. assim, podem haver varios registos pra mesma pessoa. podemos definir tipo que o registo tenha um número de 4 algarismos
% Extensão do predicado imc: Registo,Numero_do_utente,Imc_valor,Classificacao,Lim_inf,Lim_sup ↝ {V,F,D}


%------------------------------------------------------------------------------------------------
% PRESSUPOSTO DO MUNDO FECHADO
%------------------------------------------------------------------------------------------------
-utente(Nu,N,C,S,A):-nao(utente(Nu,N,C,S,A)),
                nao(excecao(utente(Nu,N,C,S,A))).
-registo(R,Nu,D,M,A,I,Al,P,Td):-nao(registo(R,Nu,D,M,A,I,Al,P,Td)),
                nao(excecao(registo(R,Nu,D,M,A,I,Al,P,Td))).
-imc(R,Nu,Imc,Cl,Linf,Lsup):-nao(imc(R,Nu,Imc,Cl,Linf,Lsup)),
                nao(excecao(imc(R,Nu,Imc,Cl,Linf,Lsup))).


%------------------------------------------------------------------------------------------------
% NEGAÇÃO POR FALHA
%------------------------------------------------------------------------------------------------
nao(Questao):- Questao,
                 !,
                 fail.
nao(Questao).


%------------------------------------------------------------------------------------------------
% EVOLUÇÃO DO CONHECIMENTO - Adicionar conhecimento à BC
%------------------------------------------------------------------------------------------------
evolucao(Termo) :-
    findall(Invariante, +Termo::Invariante, Lista),  
    insercao(Termo),
    teste(Lista).
insercao(Termo) :-assert(Termo).
insercao(Termo) :-retract(Termo),!, fail.


%------------------------------------------------------------------------------------------------
% REMOÇÃO DE CONHECIMENTO
%------------------------------------------------------------------------------------------------
remocao( Termo ) :-
    findall(Invariante, -Termo::Invariante, Lista),
    remover(Termo),
    teste(Lista).

remover(Termo):-retract(Termo).
remover(Termo):-assertz(Termo), !, fail.

teste([]).
teste([R|LR]):- R, teste(LR).


%------------------------------------------------------------------------------------------------
% INVARIANTES - Adição de restrições para a inserção e remoção de novos dados na base de dados.
%------------------------------------------------------------------------------------------------

% -----INVARIANTES INSERÇÃO DE UTENTES-----

% Garante que não ha dois utentes com o mesmo numero de utente.
+utente(Nu,N,C,S,A)::(findall((Nu),(utente(Nu,_,_,_,_)),Com),  
          comprimento(Com,X),                              e
            X==1).

% -----INVARIANTES INSERÇÃO DE REGISTO-----

% Garante que não ha dois registos de utente para o mesmo número.
% Mesmo que se crie outro registo para a mesma pessoa, por exemplo, porque mudou de cidade, tem de se criar um registo novo.
+registo(R,Nu,D,M,A,I,Al,P,Td)::(findall((R,Nu),(registo(R,Nu,_,_,_,_,_,_,_)),Com),    
            comprimento(Com,X),                              
            X==1).

% Só é possível inserir registo de utente se o utente estiver inserido.
+registo(R,Nu,D,M,A,I,Al,P,Td)::(findall((Nu),(utente(Nu,_,_,_,_)),Com),         % nao funciona
            comprimento(Com,X),                                        
            X>=1).                             
 

% Garante que um registo tem de ter mês e ano válidos e que os valores de idade, peso e altura tem de ser positivos.
+registo(R,Nu,D,M,A,I,Al,P,Td)::(     
            (D=<31,member(M, [1, 3, 5, 7, 8, 10, 12]),
            A=<2023,                
            A>=0,                                
            Al>0,
            I>0,
            P>0);

            (D=<30,member(M, [4, 6, 8,11]),
            A=<2023,              
            A>=0,
             Al>0,
            I>0,
            P>0);
            
            (D=<29,member(M, [2]),
            A=<2023,               
            A>=0,
            A mod 4=:=0,                    % Nesta parte, garante os valores de inserção para um ano bissexto
            A mod 100 =\= 0,
            Al>0,
            I>0,
            P>0);

            (D=<28,member(M, [2]),
            A=<2023,                % Aqui não precisamos de verificações específicas nos anos porque se é bissexto o programa para em cima, não entra nesta parte.
            A>=0,
            Al>0,
            I>0,
            P>0)).


% -----INVARIANTES INSERÇÃO DE IMC-----

% Garante que não ha dois registos de imc com o mesmo número para um determinado utente.
+imc(R,Nu,Imc,Cl,Linf,Lsup)::(findall((R,Nu),(imc(R,Nu,_,_,_,_)),Com), 
            comprimento(Com,X),                                
            X==1).

% Só é possível inserir registo de imc se o utente estiver inserido.
+imc(R,Nu,Imc,Cl,Linf,Lsup)::(findall((Nu),(imc(_,Nu,_,_,_,_),utente(Nu,_,_,_,_)),Com), 
            comprimento(Com,X),                                       
            X>=1). 

% O valor do imc tem de estar dentro dos limites definidos.                             
+imc(R,Nu,Imc,Cl,Linf,Lsup):: 
            (Imc=<Lsup,               
            Imc>=Linf).




%-----INVARIANTES DE REMOÇÃO-----

% Só se removem utentes se eles existirem.
-utente(Nu,N,C,S,A)::(findall((Nu),(utente(Nu,_,_,_,_)),Com),    
            comprimento(Com,X),                              
            X==0).

% Só se removem registos de informacoes do utente que existam.
-registo(R,Nu,D,M,A,I,Al,P,Td)::(findall((R,Nu),(registo(R,Nu,_,_,_,_,_,_,_)),Com),    
            comprimento(Com,X),                              
            X==0).

% Só se removem registos de imc que existam.
-imc(R,Nu,Imc,Cl,Linf,Lsup)::(findall((R,Nu),(imc(R,Nu,_,_,_,_)),Com), 
            comprimento(Com,X),                                 
            X==0).

% Função do comprimento
comprimento([],0).
comprimento([H|T],C):-comprimento(T,N), 
                    C is N+1.


%------------------------------------------------------------------------------------------------
% SISTEMAS DE INFERÊNCIA
%------------------------------------------------------------------------------------------------

% Sistema de Inferência para Questão Única
%Extensão do meta-predicado si: Questão, Resposta ↝ {V,F,D} 
si(Questao,verdadeiro):- 
        Questao.
si(Questao,falso):-
       -Questao.
si(Questao,desconhecido):- 
        nao(Questao),nao(-Questao).

% Sistema de Inferência para 2 Questões 
% Extensão do meta-predicado siM: Questão1 e/ou Questão 2, Resposta ↝ {V,F,D}  
siM(Q1 e Q2, verdadeiro):-
    si(Q1, verdadeiro),
    si(Q2, verdadeiro).
siM(Q1 e Q2, falso):-
    si(Q1, verdadeiro),
    si(Q2, falso).
siM(Q1 e Q2, desconhecido):-
    si(Q1, verdadeiro),
    si(Q2, desconhecido).
siM(Q1 e Q2, falso):-
    si(Q1, falso),
    si(Q2, verdadeiro).
siM(Q1 e Q2, falso):-
    si(Q1, falso),
    si(Q2, falso).
siM(Q1 e Q2, falso):-
    si(Q1, falso),
    si(Q2, desconhecido).
siM( Q1 e Q2, desconhecido):-
    si(Q1, desconhecido),
    si(Q2, verdadeiro).
siM(Q1 e Q2, falso):-
    si(Q1, desconhecido),
    si(Q2, falso).
siM(Q1 e Q2, desconhecido):-
    si(Q1, desconhecido),
    si(Q2, desconhecido).
siM(Q1 ou Q2, verdadeiro):-
    si(Q1, verdadeiro),
    si(Q2, verdadeiro).
siM(Q1 ou Q2, verdadeiro):-
    si(Q1, verdadeiro),
    si(Q2, falso).
siM(Q1 ou Q2, verdadeiro) :-
    si(Q1, verdadeiro),
    si(Q2, desconhecido).
siM(Q1 ou Q2, verdadeiro) :-
    si(Q1, falso),
    si(Q2, verdadeiro).
siM(Q1 ou Q2, falso):-
    si(Q1, falso),
    si(Q2, falso).
siM(Q1 ou Q2, desconhecido):-
    si(Q1, falso),
    si(Q2, desconhecido).
siM(Q1 ou Q2, verdadeiro):-
    si(Q1, desconhecido),
    si(Q2, verdadeiro).
siM(Q1 ou Q2, desconhecido):-
    si(Q1, desconhecido),
    si(Q2, falso).
siM(Q1 ou Q2, desconhecido):-
    si(Q1, desconhecido),
    si(Q2, desconhecido).


%------------------------------------------------------------------------------------------------
% AVALIADOR/ CLASSIFICADOR DO IMC                          
%------------------------------------------------------------------------------------------------
classificacao_imc(R,Nu,Imc,Classificacao,Lims):-
                registo(R,Nu,_,_,_,_,Al,P,_),
                calcular_imc(P,Al,Imc),
                Lims = [0,18.4],
                Imc<18.5,
                Imc>0,
                Classificacao=magreza;
                registo(R,Nu,_,_,_,_,Al,P,_),
                calcular_imc(P,Al,Imc),
                Lims = [18.5,24.9],
                Imc>=18.5,
                Imc=<24.9,
                Classificacao=normal;
                registo(R,Nu,_,_,_,_,Al,P,_),
                calcular_imc(P,Al,Imc),
                Lims = [25,30],
                Imc>=25,
                Imc=<30,
                Classificacao=sobrepeso;
                registo(R,Nu,_,_,_,_,Al,P,_),
                calcular_imc(P,Al,Imc),
                Lims = [30.1,39.9],
                Imc>=30.1,
                Imc=<39.9,
                Classificacao=obesidade;
                registo(R,Nu,_,_,_,_,Al,P,_),
                calcular_imc(P,Al,Imc),
                Imc>=40,
                Lims = [40,infinito], 
                Classificacao=obesidade_morbida.  


% Calculadora do IMC - Auxiliar                  
calcular_imc(P,Al,Imc_valor):-              
            Imc_valor is P/((Al/100)*(Al/100)). 


           
%-----------------------------------------------------------------
% VÁRIOS TIPOS DE CONHECIMENTO
%-----------------------------------------------------------------

% ----- CONHECIMENTO PERFEITO-----
utente(1,maria,braga,f,nao).
registo(r1,1,24,10,2023,30,163,55,boa).
imc(r1,1,20.7,normal,18.5,24.9).

utente(2,nuno,evora,m,sim).
registo(r1,2,24,10,2023,56,179,86,boa).
imc(r1,2,26.8,sobrepeso,24.9,30).

% -----CONHECIMENTO IMPERFEITO INCERTO-----

excecao(utente(Nu,N,C,S,A)):-utente(Nu,N,C,S,nao_sabe).
% O utente com número 3, Francisca, é adotada, não conhecendo a sua família biológica não sabe se tem ou nao antecentes familiares.
utente(3,francisca,povoa,f,nao_sabe).
registo(r1,3,20,09,2021,13,157,44,ma). 
imc(r1,3,17.9,magreza,0,18.5).                      % não sabe se tem antecedentes familiares
registo(r2,3,22,09,2022,14,161,46,ma).              % segundo registo do utente 3            
imc(r2,3,17.7,magreza,0,18.5).

excecao(registo(R,Nu,D,M,A,I,Al,P,Td)):-registo(R,Nu,D,M,A,I,nao_sabe,nao_sabe,Td).
% Quando o utente com número 4, Joana, se foi registar, a balança e o estadiómetro não estavam calibrados, não se tendo realizado medições.
utente(4,joana,porto,f,nao).
registo(r1,4,23,07,2020,34,nao_sabe,nao_sabe,boa).  % não sabe quanto mede e quanto pesa

% -----CONHECIMENTO IMPERFEITO IMPRECISO-----

% Quando o utente com número 5, Alberto,se foi rgistar, o estadiómetro não estava calibrado,não se tendo obtido uma medição precisa.
utente(5,alberto,faro,m,nao).                  
excecao(registo(r1,5,23,02,2020,31,A,78,boa)):-     % não tem a certeza de quanto mede
            A>=175,
            A=<185.

% Os registos da semana em que o utente com número 6, Filipa, se foi registar ficaram com datas trocadas, não sendo possível saber exatamente a data.
utente(6,filipa,guimaraes,f,sim).
excecao(registo(r1,5,23,01,2018,31,168,60,boa)).    % não se lembra em que dia foi feito o registo
excecao(registo(r1,5,24,01,2018,31,168,60,boa)).


% -----CONHECIMENTO IMPERFEITO INTERDITO-----

%Ao fazer o registo da Cleopatra, uetnete com número 7, não sabemos se esta tinha antecedentes familiares,
%nem sabemos os seus dados de saúde, ltura, peso... e nunca vamos saber...
excecao(registo(R,Nu,D,M,A,I,Al,P,Td)):-registo(R,Nu,algum_dia,algum_mes,algum_ano,alguma_idade,alguma_altura,algum_peso,alguma_alimentacao).
interdito(algum_dia,algum_mes,algum_ano,alguma_idade,alguma_altura,algum_peso,alguma_alimentacao).
utente(7,cleopatra,cairo,f,nao_sabe). % neste caso, temos aqui conhecimento incerto. não se sabe se a cleopatra tinha antecedentes familiares de obesidade
registo(r1,7,algum_dia,algum_mes,algum_ano,alguma_idade,alguma_altura,algum_peso,alguma_alimentacao). 
+registo(R,Nu,D,M,A,I,Al,P,Td)::(findall((D,M,A,I,Al,P,Td),(registo(r1,7,D,M,A,I,Al,P,Td),nao(interdito(D,M,A,I,Al,P,Td))),S),
                       comprimento(S,N),                                       
                       N==0).                     % nao temos forma de saber nenhum dado de saude da cleopatra 

%O Presidente da República registou-se mas não é permitido saber qual a data do registo, nem nenhum dado a este associado, devido ao seu estatuto.
utente(8,marcelo,celorico,m,sim).
registo(r1,8,algum_dia,algum_mes,algum_ano,alguma_idade,alguma_altura,algum_peso,alguma_alimentacao).
+registo(R,Nu,D,M,A,I,Al,P,Td)::(findall((D,M,A,I,Al,P,Td),(registo(r1,8,D,M,A,I,Al,P,Td),nao(interdito(D,M,A,I,Al,P,Td))),S),
                       comprimento(S,N),        
                       N==0).                     % aqui também não nos é permitido saber nenhum dado de saúde sobre o presidente da República


%-----CONHECIMENTO POSITIVO E NEGATIVO------
utente(9,alberto,tomar,m,nao).
registo(r1,9,04,11,2023,43,171,68,boa).                                                         
-imc(r1,9,27.2,obesidade,30.1,39.9).        % conhecimento negativo. este registo é falso       
imc(r1,9,23.3,normal,18.5,24.9).        % este é o verdadeiro registo                                