/*
 * @Date: 2022-01-05 10:13:12
 * @Description: 个人中心web页面引擎
 * @FilePath:
 */
import {
  Cookies,
  DataHandleUtils,
  Layout,
  PlatformUtils,
  RouterUtils,
  screenSize,
  t,
  TimeUtils,
  WithTheme,
  BuildParams,
  EVENT_TYPE,
  EventTracking,
  HttpService,
  LoginUtils,
  CookieUtils,
  Service as env,
  ERROR_TYPE,
  MCP_PORTAL,
  PAGE_TYPE,
  PORTALSTR,
  URL_CONSTANTS,
  DynamicComponent,
  FooterNavigationStore,
  AppStore,
  onLayout,
  layout,
  SubTabsStore,
  CommonUtils,
  Listener,
  cacheUtils,
} from '@hw-vmall/vrn-basic-comp';
import {
  Toast,
  CommonErrorPage,
  PlaceHolder,
  FixedButton,
  ToolBar,
  Deposit,
  GroupDialog,
  Privacy,
  dialogOrderStore,
  dialogOrderManager,
  groupDialogManager,
  jsonConvert,
  FooterNavigation,
  ScenePurchaseBottomNavLayout,
} from '@hw-vmall/vrn-bussiness-comp';
import { observer } from 'mobx-react';
import React from 'react';
import { Animated, AppState, DeviceEventEmitter, Dimensions, Platform, Text, View, ScrollView } from 'react-native';
import Menu from '../../../../component/basic2/navigation';
import { MapComponents } from '../../../../common/maps/map-components';
import PersonalHead from '../../component/personal';
import PersonalTitle from '../../component/personal/personal-head';
import PerrsonalStyle from './style';

const dsWindow = Dimensions.get('window');
let scrollTimer: any;
const size = screenSize(dsWindow.width);

let portal = MCP_PORTAL.WAP;
let portalStr = PORTALSTR[MCP_PORTAL.WAP];
let webDomain = env.wapDomain;
if (PlatformUtils.isPc(dsWindow.width)) {
  portal = MCP_PORTAL.WEB;
  portalStr = PORTALSTR[MCP_PORTAL.WEB]; // 这里是字符串PC,不是WEB
  webDomain = env.webDomain;
}
let screenWidth = 0;
if (PlatformUtils.isWeb()) {
  screenWidth = window.screen.width;
}

// 功能开关 11.5关闭 11.6上线
const IS_RN_POPUP_MESSAGE_OPEN = true;

@observer
class PerrsonalDefault extends React.Component<any, any> {
  private scroller: any;
  windowsListener: any;
  loginListener: any;
  headStyle: any = {};
  titleStyle: any = {};
  tabs: [];
  tabConfig: '';
  homeScrollListener: any;
  cardId: '';
  portal: number;
  strategyIdList = '';
  bgColor: string = '';
  isShow: boolean = false;
  // 1-空页面 2-带子页签的空页面 3-分类页 4-个人中心 7-秒杀页
  pageType: number = 4;
  convertResult: any = {};
  personalStyleChange: any = {};
  currentTime: number = new Date().getTime();
  otherParams: any = {};
  cartTimer: NodeJS.Timeout;
  menuConfig: any = {
    showSearch: 'true',
    searchHotListShow: 'true',
    searchResultPageProdShow: 'true',
    searchResultPageContentShow: 'true',
    searchResultPageActivityShow: 'true',
    showCategory: 'true',
  };
  pageCatCode: string = '';
  pageCatName: string = '';
  tid: string = '';
  dialogEventLisenter: any = null;
  sonRef: any = null;
  changeOtherDialogTimer: any = null;
  openDmpDialogTimer: any = null;
  isGroupFlag: boolean = false;
  isDisplayScenePurchaseNavBottom: boolean = false; // 是否展示场景购的底部导航
  scenePurchaseNavBottomData: any = {}; // 场景购底部导航的数据
  pageListener: Listener = new Listener('Personal');
  constructor(props: any) {
    super(props);
    this.state = {
      scrollY: new Animated.Value(0),
      pageId: props.pageId,
      pageAlias: null,
      strategyIdList: null,
      cmsData: { pageInfos: [] },
      // loading标记
      loading: true,
      // 防止连续下拉
      isRefreshing: false,
      // error标记
      error: false,
      titleOpacity: 0,
      freshTab: true,
      cartNum: 0, // 购物车数量
      messageNum: 0, // 消息中心数量
      currentTabIndex: 0,
      isClickTab: false,
      errorType: ERROR_TYPE.OTHER_ERROR,
      appState: AppState.currentState,
      loadState: 1,
      navData: '',
      configInfo: this.menuConfig,
      iconConfigInfo: {},
      avaImg: '',
      userName: '',
      userLevel: 0,
      mpUid: '',
      isJsLogin: false,
      isShowMember: false,
      isVpro: '',
      showBox: 0,
      withNoLoginUser: 0,
      userAccount: this.props.userAccount,
    };
    this.otherParams.pageListener = this.pageListener;
  }

  componentDidUpdate() {
    // JEST用来测试渲染次数
  }

  async componentDidMount() {
    cacheUtils.refreshCacheStrategy();
    this.handleUrlParams();
    await this._isLogin();
    this.loginListener = DeviceEventEmitter.addListener('popupLoginSuccess', () => {
      this._isLogin();
    });
    // 更新系统时间
    TimeUtils.updateSystemTime();
    this.getWebPageInfo();
    // wap需要在获取页头配置时，来判断是否调购物车接口
    PlatformUtils.isPc(dsWindow.width) && await this._getCartNum();
    // 获取消息中心数据
    HttpService.getNewMessageNum.bind(this)();
    // 绑定事件
    this.handleAddListeners();
    PlatformUtils.isPc(dsWindow.width) && this.setNavData();
    // 横屏刷新页面
    if (PlatformUtils.isWap) {
      this.windowsListener = window.addEventListener('orientationchange', (event) => {
        if (
          event.target.screen.orientation.angle === 90 ||
          event.target.screen.orientation.angle === 0 ||
          event.target.screen.orientation.angle === 270 ||
          event.target.screen.orientation.angle === 180
        ) {
          window.location.reload();
        }
      });
      window.addEventListener('resize', this.handleResize);
    }
    this.getVproLogo();
    this.dialogEventLisenter = DeviceEventEmitter.addListener('getBenefitSucc', () => {
      this.sonRef?.getAssterInfo();
    });
    if (PlatformUtils.isWeb()) {
      CommonUtils.getRecommendConfigRes();
    }
  }

  componentWillUnmount() {
    this.loginListener && this.loginListener.remove();
    this.state.scrollY && this.state.scrollY.removeAllListeners();
    this.homeScrollListener?.remove();
    this.dialogEventLisenter && this.dialogEventLisenter.remove();
    window.removeEventListener('unload', this.unload);
    window.removeEventListener('scroll', this._onMomentumScrollEnd);
    window.removeEventListener('resize', this.handleResize);
    this.windowsListener && window.removeEventListener('orientationchange', () => {});
    this.changeOtherDialogTimer?.remove();
    scrollTimer && clearTimeout(scrollTimer);
  }

  handleResize = () => {
    if (Math.abs(window.screen.width - screenWidth) > 200) {
      window.location.reload();
    }
  };

  // 登录状态传递
  async _isLogin() {
    const isLogin = AppStore.isLogin ?? ((await LoginUtils.getLoginStatus()) as Boolean);
    AppStore.setIsLogin(isLogin);
    this.setState({ isJsLogin: isLogin }, () => {
      if (isLogin) {
        this._queryUserInfo();
      }
    });
  }
  // componentDidMount里的绑定事件放在这里，方便后期维护
  handleAddListeners = () => {
    // 监听PC端页面滚动事件
    window.addEventListener('scroll', this._onMomentumScrollEnd);
    window.addEventListener('unload', this.unload);
    // 监听子页签切换页面时，调整页面的纵向滚动条位置，使每次切换完页签后， 子页签容器的内容处于容器中开始位置
    this.homeScrollListener = DeviceEventEmitter.addListener('homeScrollTo', this.onTabChanged);
  };
  getWebPageInfo() {
    let tid = Cookies.get('TID') || this.getRandomTid();
    let abData = JSON.parse(sessionStorage.getItem('abData'));
    if (!CommonUtils.isEmpty(abData)) {
      this.setAbData(abData?.strategyInfoList || []);
      abData?.tabInfos.length && this.setWapFooterNavigation(abData?.tabInfos);
    } else {
      CookieUtils.getStrategyForWebWap(tid, portal.toString()).then((res) => {
        if (res?.code === '0' || res?.success === true) {
          sessionStorage.setItem('abData', JSON.stringify(res));
          this.setAbData(res?.strategyInfoList || []);
          res.tabInfos.length && this.setWapFooterNavigation(res.tabInfos);
        }
      });
    }
  }
  // 付费会员logo
  getVproLogo = () => {
    const holderparams = 'vmall_vpro_logo';
    HttpService.getTemplate(holderparams).then((res) => {
      if (res?.success) {
        const tmpMap: any = res.templateMapping;
        const tagHolder = tmpMap?.vmall_vpro_logo?.content?.replace(/<.*?>/gi, '');
        this.otherParams.vproLogoTagHolder = tagHolder;
      }
    });
  };
  // 设置导航数据
  setNavData = () => {
    const parmas = {
      subType: 'commonNavigation',
      portal: '1',
    };
    HttpService.getGlobalDataSource(parmas).then((res) => {
      Object.keys(res.dataSource).forEach((a) => {
        this.setState({
          navData: res.dataSource[a].dataInfos,
        });
      });
    });
  };

  isPc = () => {
    return PlatformUtils.isPc(dsWindow.width);
  };
  _queryUserInfo = () => {
    const portal = CommonUtils.getPortal();
    HttpService.getUserInfo(portal)
      .then((user: any) => {
        const userInfo = user?.userInfo || {};
        AppStore.setUserInfo(user?.userInfo);
        if (userInfo.groupId) {
          Cookies.set('isGroupUser', 'true', {
            path: '/',
            domain: '.vmall.com',
          });
          Cookies.set('groupflag', 'true', {
            path: '/',
            domain: '.vmall.com',
          });
          this.isGroupFlag = true;
        } else {
          Cookies.set('isGroupUser', 'false', {
            path: '/',
            domain: '.vmall.com',
          });
          Cookies.set('groupflag', null, {
            path: '/',
            domain: '.vmall.com',
          });
          this.isGroupFlag = false;
        }
        this.otherParams.userInfo = userInfo;
        const uid = userInfo.uid;
        this.setState({
          avaImg: userInfo.custHeaderImg,
          userName: userInfo.nickName,
          userLevel: userInfo.custGrad,
          mpUid: userInfo.mpUid,
          isVpro: userInfo.isVpro,
          userAccount: userInfo.userAccount,
        });
        groupDialogManager.getGroupAD(uid);
        groupDialogManager.getPrivacy(uid);
      })
      .catch(() => {
        this.otherParams.userInfo = null;
        groupDialogManager.getGroupAD();
        groupDialogManager.getPrivacy();
      });
  };

  // 页面载入的埋点
  eventTracingReportByLoad = () => {
    let actionCode = this.isPc() ? '310000000' : '210000000';
    EventTracking.eventTracingReportRightNow({
      actionCode: actionCode,
      actionName: '加载个人中心组件化页面',
      eventType: EVENT_TYPE.EVENT_TYPE_LOADING_PAGE,
      pageId: String(env.pageId),
      content: {
        load: '1',
      },
      pageCatCode: this.pageCatCode,
      pageCatName: this.pageCatName,
      resSiteCode: '',
      resSiteName: '',
    });
  };

  // 子页签切换
  onTabChanged = (data: any) => {
    if (data.navTop) {
      this.scroller && this.scroller.scrollTo({ y: data.stickyLayoutY, animated: true });
    }
  };

  /**
   * 获取Web pageID和AB策略
   * @private
   */
  _getWebPageInfo = () => {
    return LoginUtils.getStatus()
      .then(() => {
        // AB策略没拿到，直接调用page接口。
        return HttpService.getPageInfoListAsync(
          this.state.pageId || '',
          this.state.strategyIdList,
          '',
          '',
          '',
          this.state.pageAlias,
        );
      })
      .then((data: any) => {
        // 变装组件顺序按列表顺序重排
        data = DataHandleUtils.initCardsList(data, 'web');
        const pageId = this.handlePageInfos(data);
        this.headStyle = JSON.parse(data.pageInfos[0].headerStyle);
        // wap页头是否配置购物车
        const wapHasCartIcon = this.headStyle?.iconTexts?.some((item: any) => item?.iconAttribute === 'cart');
        wapHasCartIcon && PlatformUtils.isWap(dsWindow.width) && this._getCartNum();
        this.setState(
          {
            iconConfigInfo:
              data?.pageInfos?.length && JSON.stringify(JSON.parse(data?.pageInfos[0].headerStyle)?.attribute),
            cmsData: data,
            pageId,
          },
          () => {
            this.handleTitleStyle();
            // cmsData处理
            this._pageDataHandle();
          },
        );
        this.eventTracingReportByLoad();
        DataHandleUtils.oneTimeCallPageDataSource(data?.pageInfos);
        DataHandleUtils.updateSEOContent(data?.pageInfos, this.props.pageType);
        return Promise.resolve();
      })
      .catch(() => {
        this.eventTracingReportByLoad();
      });
  };

  private handlePageInfos(data: any) {
    let pageId;
    if (data?.pageInfos?.length) {
      pageId = String(data.pageInfos[0].pageId);
      env.pageId = pageId;
      env.appid = data.pageInfos[0].channel;
      const tabs = data.pageInfos[0]?.tabInfos || [];
      const headStyle = JSON.parse(data.pageInfos[0].headerStyle);
      this.personalStyleChange =
        data?.pageInfos.length && data?.pageInfos[0]?.styleChange ? JSON.parse(data?.pageInfos[0]?.styleChange) : {};
      const titleHeight = this.headStyle?.headStyle && size !== 'large' ? 56 : 0;
      this.otherParams.hasTabTop = tabs?.length > 1;
      this.otherParams.hasTitle = !!headStyle?.headStyle;
      this.otherParams.isLogin = this.state.isJsLogin;
      this.otherParams.isGroupFlag = this.isGroupFlag;
      this.convertResult = jsonConvert(data.pageInfos[0], PAGE_TYPE.personal, titleHeight, true, this.otherParams);
      const { pageCatCode, pageCatName, pageParam } = data?.pageInfos[0] || {};
      this.pageCatCode = pageCatCode;
      this.pageCatName = pageCatName;
      const param = pageParam && JSON.parse(pageParam);
      this.setState({
        showBox: param?.showBox,
        withNoLoginUser: param?.withNoLoginUser,
      });
      data?.pageInfos[0]?.cards?.map((card) => {
        if (card.cardType === 'menu') {
          const conf = JSON.parse(card.configInfo);
          this.menuConfig = card.configInfo;
          const tempConfigInfo = {
            showSearch: 'true',
            searchHistoryShow: conf.searchHistoryShow,
            searchHotListShow: conf.searchHotListShow,
          };
          this.setState({
            configInfo: tempConfigInfo,
          });
        }
      });
    }
    return pageId;
  }

  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  _getPageInfo(data?: boolean) {
    return this._getWebPageInfo()
      .catch((e) => {
        // 网络错误
        let errorType = ERROR_TYPE.OTHER_ERROR;
        if (e?.message?.includes('Network Error')) {
          errorType = ERROR_TYPE.NETWORK_ERROR;
          this.setState({
            errorType,
          });
        } else {
          errorType = ERROR_TYPE.OTHER_ERROR;
          // 其他错误
          this.setState({
            errorType,
          });
        }
        // 流程出错
        this.setState({
          error: true,
          loadState: 2,
        });
      })
      .finally(() => {
        // 结束loading状态
        this.setState({
          loading: false,
          isRefreshing: false,
        });
        return Promise.resolve();
      });
  }

  handleTitleStyle = () => {
    const { cmsData } = this.state;
    if (cmsData?.pageInfos?.length) {
      const { pageId, styleChange, groupStyleChanges } = cmsData.pageInfos[0];
      this.titleStyle = {
        cardId: pageId,
        styleChange: styleChange ? JSON.parse(styleChange) : '',
        groupStyleChanges: groupStyleChanges ? JSON.parse(groupStyleChanges) : '',
      };
      if (this.titleStyle.styleChange) {
        if (Number(this.titleStyle.styleChange.bgFill) === 1 && this.titleStyle.styleChange.bgColor) {
          this.bgColor = this.titleStyle.styleChange.bgColor;
        }
        SubTabsStore.onSubTabsUpdate(this.titleStyle.styleChange);
      } else if (this.titleStyle.groupStyleChanges && this.titleStyle.groupStyleChanges[0]) {
        // 如果styleChange里没有页头的变装配置，去groupStyleChanges找
        this.titleStyle.groupStyleChanges.forEach((item) => {
          // 根据pageId找对应的配置
          if (item?.cardIds?.includes(String(pageId))) {
            this.titleStyle.styleChange = item.styleChange;
            if (Number(item.styleChange.bgFill) === 1 && item.styleChange.bgColor) {
              this.bgColor = item.styleChange.bgColor;
            }
            SubTabsStore.onSubTabsUpdate(item.styleChange);
          }
        });
      }
    }
  };

  _pageDataHandle() {
    const { cmsData } = this.state;
    if (cmsData?.pageInfos?.length) {
      this.tabs = cmsData.pageInfos[0]?.tabInfos || [];
      this.tabConfig = cmsData.pageInfos[0]?.cards?.map((card) => {
        if (card.cardType === 'sub_tab') {
          this.cardId = card.cardId;
          return card.configInfo;
        }
      });
      this.headStyle = JSON.parse(cmsData.pageInfos[0].headerStyle);
      this.pageType = cmsData.pageInfos[0]?.pageType;
    }
  }

  // 获取购物车数据
  async _getCartNum() {
    const res = await HttpService.getTotalNum() || {};
    const { info = '', data = 0 } = res;
    if (info === 'success') {
      this.setState({
        cartNum: data > 99 ? 99 : data,
      }, () => {
        AppStore.setCartNum(this.state.cartNum);
        DeviceEventEmitter.emit('refreshCartNum');
      });
    }
  }

  // 回到顶部
  onBackTop = () => {
    this.scroller && this.scroller.scrollTo({ y: 0, animated: true });
  };
  _onMomentumScrollEnd = (e: any) => {
    this.setState({
      titleOpacity:
        e.srcElement.scrollingElement.scrollTop / 56 >= 1 ? 1 : e.srcElement.scrollingElement.scrollTop / 56,
    });
    scrollTimer && clearTimeout(scrollTimer);
    scrollTimer = setTimeout(() => {
      // 监听页面滚动事件
      DeviceEventEmitter.emit('onScrollEvent', '', 'personal');
    }, 300);
    if (PlatformUtils.isWap(dsWindow.width)) {
      const pageYOffset = window?.pageYOffset || 0;
      DeviceEventEmitter.emit('onOutScrollViewScroll', pageYOffset, PAGE_TYPE.personal);
    }
  };
  setAbData(list: Array<any>) {
    let abArr = list?.map((el) => {
      return el.strategyId || '';
    });
    env.strategies = abArr.join(',');
    let strategyIdList = JSON.stringify(abArr);
    this.setState({ strategyIdList }, () => {
      this._getPageInfo();
      return Promise.resolve();
    });
  }
  setWapFooterNavigation(tabInfos) {
    // 鸿蒙单框架app不展示底部导航
    if (CommonUtils.isHmshop()) {
      return;
    }
    let tabs: any = [];
    for (let i = 0; i < tabInfos.length; i++) {
      if (tabInfos[i].tabType !== 'smarthome') {
        tabs.push(tabInfos[i]);
      }
      if (tabInfos[i]?.tabType === 'category') {
        if (tabInfos[i]?.relatedPageType === '1') {
          let CURL = webDomain + URL_CONSTANTS.CATEGORY_URL_WEB_NEW + tabInfos[i]?.relatedPage;
          Cookies.set('rncategoryviewurl', CURL, { path: '/', domain: '.vmall.com' });
        } else {
          Cookies.set('rncategoryviewurl', null, { path: '/', domain: '.vmall.com' });
        }
      }
    }
    FooterNavigationStore.setTabInfos(tabs);
  }
  // 获取底部TAB数据
  getWapFooterNavigation() {
    // 鸿蒙单框架app不展示底部导航
    if (CommonUtils.isHmshop()) {
      return;
    }
    let tid = Cookies.get('TID') || this.getRandomTid();
    return new Promise((resolve) => {
      CookieUtils.getStrategyForWebWap(tid, MCP_PORTAL.WAP.toString())
        .then((res: any) => {
          if (res.tabInfos) {
            let tabInfos: any = [];
            for (let i = 0; i < res.tabInfos.length; i++) {
              if (res.tabInfos[i].tabType !== 'smarthome') {
                tabInfos.push(res.tabInfos[i]);
              }
              if (res.tabInfos[i]?.tabType === 'category') {
                if (res.tabInfos[i].relatedPageType === '1') {
                  const categoryUrl = webDomain + URL_CONSTANTS.CATEGORY_URL_WEB_NEW + res.tabInfos[i]?.relatedPage;
                  Cookies.set('rncategoryviewurl', categoryUrl, {
                    path: '/',
                    domain: '.vmall.com',
                  });
                } else {
                  Cookies.set('rncategoryviewurl', null, {
                    path: '/',
                    domain: '.vmall.com',
                  });
                }
              }
            }
            FooterNavigationStore.setTabInfos(tabInfos);
          } else {
            return Promise.resolve();
          }
        })
        .finally(() => {
          // @ts-expect-error 忽略TS检查
          resolve();
        });
    });
  }
  getRandomTid = () => {
    let s = [];
    let h = '0123456789abcdef';
    for (let a = 0; a < 32; a++) {
      s[a] = h.substr(Math.floor(Math.random() * 16), 1);
    }
    s[14] = '4';
    s[19] = h.substr((s[19] & 3) | 8, 1);
    s[8] = s[13] = s[18] = s[23];
    let tid = s.join('');
    return tid;
  };
  _onScrollBeginDrag = (e: any) => {
    // 监听页面滚动开始事件
    DeviceEventEmitter.emit('onScrollBeginDragEvent', e);
  };

  // 页面离开
  unload = () => {
    if (typeof navigator?.sendBeacon === 'function') {
      let actionCode = this.isPc() ? '310000011' : '210000011';
      let body = [
        BuildParams.buildWebWapPostParams({
          actionCode: actionCode,
          actionName: '离开个人中心页面上报',
          eventType: EVENT_TYPE.EVENT_TYPE_LEAVE,
          pageId: String(env.pageId),
          content: {},
          pageCatCode: this.pageCatCode,
          pageCatName: this.pageCatName,
          resSiteCode: '',
          resSiteName: '',
        }),
      ];
      let headers = {
        type: 'application/json',
        language: 'zh-CN',
        encoding: 'gzip',
        data: new Date().getTime(),
      };
      let blobPerson = new Blob([JSON.stringify(body)], headers);
      navigator.sendBeacon(`${env.reportBatchUrl}`, blobPerson);
    }
  };

  _onLayout = (e: any) => {
    onLayout(e);
    layout(e, PAGE_TYPE.personal);
  };

  handleUrlParams = () => {
    // 获取url中携带的参数
    const propStr = window?.location?.search?.substring(1) || '';
    const propArr = propStr?.split('&') || [];
    propArr.forEach((el) => {
      let arr = el.split('=');
      if (!this.state.pageId) {
        if (arr[0] === 'pageId') {
          env.pageId = arr[1];
          FooterNavigationStore.getPageId(arr[1]);
          FooterNavigationStore.setPageName('Personal');
          this.setState({
            pageId: arr[1],
          });
        } else if (arr[0] === 'pn') {
          this.setState({
            pageAlias: arr[1],
          });
        }
      }
    });
  };

  render() {
    const { isRefreshing, loading, pageId, cmsData, error, pageAlias } = this.state;
    return !isRefreshing && loading ? (
      <PlaceHolder />
    ) : (
      ((pageId || pageAlias) && cmsData && cmsData?.pageInfos?.length && !error && this._loadPage()) ||
        this._loadErrorPage()
    );
  }
  // 容错
  _loadErrorPage = () => {
    return (
      <WithTheme themeStyles={PerrsonalStyle}>
        {(styles) => {
          return <CommonErrorPage errorType={this.state.errorType} />;
        }}
      </WithTheme>
    );
  };

  /**
   * 根据order类型获取Dialog的视图
   * @param order
   */
  getDialogViewByOrder = (order: dialogOrderManager.Order) => {
    let orderTypes = dialogOrderManager.getOrderTypes();
    let Order = dialogOrderManager.Order;
    let curOrderType = null;
    if (!orderTypes) {
      return null;
    }
    for (const orderType of orderTypes) {
      if (orderType.order === order) {
        curOrderType = orderType;
        break;
      }
    }
    if (!curOrderType) {
      return null;
    }
    let info = null;
    switch (order) {
      case Order.ORDER_PRIVACY:
        info = curOrderType.info;
        sessionStorage.setItem(`IS_POPUP_MESSAGE_SHOW_${this.state.pageId}`, '1');
        return (
          <Privacy
            info={info}
            setSaleInfoCfgOff={HttpService.setSaleInfoCfgOff}
            setSaleInfoCfgOn={HttpService.setSaleInfoCfgOn}
            signingResults={HttpService.signingResults}
            pageId={this.state.pageId}
            userInfo={this.otherParams?.userInfo}
          />
        );
      case Order.ORDER_GROUP:
        info = curOrderType.info;
        sessionStorage.setItem(`IS_POPUP_MESSAGE_SHOW_${this.state.pageId}`, '1');
        return (
          <GroupDialog
            actionUrl={info.adPrdUrl}
            imgUlr={info.adPicUrl}
            imgWidth={info.width}
            imgHeight={info.height}
            pageId={this.state.pageId}
          />
        );
      case Order.ORDER_DEPOSIT:
        info = curOrderType.info;
        sessionStorage.setItem(`IS_POPUP_MESSAGE_SHOW_${this.state.pageId}`, '1');
        return <Deposit data={info} pageId={this.state.pageId} />;
      default:
        break;
    }
    return null;
  };

  goHome = () => {
    RouterUtils.gotoPage('/', true);
  };

  // 调用子组件方法
  refSon = (ref) => {
    this.sonRef = ref;
  };

  private renderPersonalTitle(vproList) {
    const disPlay = vproList?.display;
    const isDisplayVPro =
      String(disPlay) === '1' &&
      String(this.props.enableAdvancedFeature) !== '0' &&
      !this.isPc();
    const isMember = isDisplayVPro && String(this.state.isVpro) === '1' && this.props.isLogin;
    return (
      <View
        style={{
          position: 'fixed',
          top: 0,
          left: 0,
          elevation: 2,
          zIndex: 1,
          width: '100%',
          height: 56,
        }}
      >
        <PersonalTitle
          configInfo={this.state.iconConfigInfo}
          isLogin={this.state.isJsLogin}
          isMember={isMember}
          avaImg={this.state.avaImg}
          userName={this.state.userName}
          titleOpacity={this.state.titleOpacity}
          cartNum={this.state.cartNum}
          userLevel={this.state.userLevel}
          messageNum={this.state.messageNum}
          headStyle={this.headStyle}
          groupStyleChanges={this.titleStyle.groupStyleChanges}
          pageId={this.state.pageId}
          mpUid={this.state.mpUid}
          personalStyleChange={this.personalStyleChange}
          vproList={vproList}
          isVpro={this.state.isVpro}
        />
      </View>
    );
  }

  _loadPage = () => {
    let vproList = [];
    let Order = dialogOrderManager.Order;
    this.convertResult?.children?.forEach((item) => {
      if (item.type === 'premiumMember') {
        vproList = item.props.configInfo;
      }
    });
    const convertResult = jsonConvert(
      this.state?.cmsData?.pageInfos[0],
      PAGE_TYPE.personal,
      undefined,
      false,
      this.otherParams,
    );
    let scenePurchaseNavBottomPlacement = { isShowUp: false, showUpHeight: 0 };
    if (convertResult?.scenePurchaseNavBottom?.isDisplay) {
      scenePurchaseNavBottomPlacement.isShowUp = true;
      scenePurchaseNavBottomPlacement.showUpHeight = 56;
      this.isDisplayScenePurchaseNavBottom = true;
      this.scenePurchaseNavBottomData = convertResult?.scenePurchaseNavBottom?.scenePurchaseNavBottomData;
    }
    const isWap = PlatformUtils.isWap(dsWindow.width);
    const isPc = PlatformUtils.isPc(dsWindow.width);
    return (
      <>
        {dialogOrderStore.curDialogOrder !== Order.ORDER_NONE &&
          this.getDialogViewByOrder(dialogOrderStore.curDialogOrder)}
        <WithTheme themeStyles={PerrsonalStyle}>
          {(styles, theme) => {
            return (
              <>
                {isWap && this.renderPersonalTitle(vproList)}
                <ScrollView
                  style={[
                    styles.viewStyle,
                    {
                      minHeight: dsWindow.height,
                      marginBottom: size === 'large' ? 0 : FooterNavigationStore.barHeight,
                    },
                  ]}
                  onLayout={this._onLayout}
                  nativeID="personal_no_focus_outline"
                >
                  {/* 首页我的商城 */}
                  {isPc && (
                    <View style={{ zIndex: 2 }}>
                      <ToolBar />
                      <Menu categoryList={this.state.navData} configInfo={this.state.configInfo} />
                      <View style={styles.titleWrapper}>
                        <Text
                          onPress={() => {
                            this.goHome();
                          }}
                          numberOfLines={1}
                          ellipsizeMode="tail"
                          style={styles.tabHome}
                        >
                          {t('tab_index')}
                        </Text>
                        <Text style={styles.dayu}>&gt;</Text>
                        <Text style={styles.myshop}>{t('my_mall')}</Text>
                      </View>
                    </View>
                  )}
                  {/* 头部固定区域 */}
                  <Layout
                    style={{
                      zIndex: 1,
                    }}
                  >
                    <PersonalHead
                      configInfo={this.state.iconConfigInfo}
                      isLogin={this.state.isJsLogin}
                      avaImg={this.state.avaImg}
                      userName={this.state.userName}
                      userAccount={this.state.userAccount}
                      titleOpacity={this.state.titleOpacity}
                      cartNum={this.state.cartNum}
                      userLevel={this.state.userLevel}
                      messageNum={this.state.messageNum}
                      headStyle={this.headStyle}
                      groupStyleChanges={this.titleStyle.groupStyleChanges}
                      pageId={this.state.pageId}
                      mpUid={this.state.mpUid}
                      personalStyleChange={this.personalStyleChange}
                      vproList={vproList}
                      isVpro={this.state.isVpro}
                      ref={this.refSon}
                    />
                  </Layout>
                  <View
                    style={{
                      marginTop: 12,
                      alignItems: 'center',
                    }}
                  />
                  {/* 组件渲染 */}
                  <DynamicComponent
                    // @ts-expect-error 忽略TS检查
                    {...this.convertResult}
                    mapComponents={MapComponents}
                    stickyScrollY={this.state.scrollY}
                    navigation={this.props.navigation}
                  />
                  {this.isDisplayScenePurchaseNavBottom && (
                    <View
                      style={{
                        height: 24 + this.scenePurchaseNavBottomData?.bottomNavHeight,
                      }}
                    />
                  )}
                </ScrollView>
                {/* 浮标 */}
                <FixedButton
                  {...this.convertResult}
                  cartNum={this.state.cartNum}
                  messageNum={this.state.messageNum}
                  pageId={this.state.pageId}
                />
                {isWap && FooterNavigationStore.tabInfos.length !== 0 ? (
                  // wap显示底部页签
                  <FooterNavigation
                    pageType={'personal_center'}
                    tabInfos={FooterNavigationStore.tabInfos.slice(0, 5)} // 最多只展示5个页签
                  />
                ) : null}
                <Toast pageType={PAGE_TYPE.personal} />
                {this.isDisplayScenePurchaseNavBottom && (
                  <ScenePurchaseBottomNavLayout
                    scenePurchaseBottomNavData={this.scenePurchaseNavBottomData}
                    scenePurchaseNavBottomPlacement={scenePurchaseNavBottomPlacement}
                  />
                )}
              </>
            );
          }}
        </WithTheme>
      </>
    );
  };
}
export default PerrsonalDefault;
